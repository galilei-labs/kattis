(* Implementation of segmentintersection (segmentintersection.spec):
   CLRS 33.1-style exact intersection of two closed segments A-B and C-D,
   straight-line code on 63-bit words read through Sint63, no Z, no float,
   no division, no loop.

   Code ([isect_m]).  r = B - A, s = D - C, q = C - A,
   den = cross(r,s), tn = cross(q,s), un = cross(q,r).
   - den <> 0 (lines cross): sign-normalise (den, tn, un) so den > 0; the
     answer is Point (x1*den + tn*rx) (y1*den + tn*ry) den when
     0 <= tn <= den and 0 <= un <= den, else Empty.
   - den = 0 and A = B: Point A if A lies on C-D, else Empty;
     den = 0 and C = D: Point C if C lies on A-B, else Empty.
   - den = 0, both proper, un <> 0 (parallel distinct lines): Empty.
   - den = 0, un = 0 (collinear): sort each segment's ends
     lexicographically (x, then y), intersect [max lows, min highs]:
     Segment lo hi when lo < hi, Point lo when lo = hi, else Empty.
   Under |coordinate| <= 10^4 every value fits easily: |den|,|tn|,|un|
   <= 8*10^8, the point's numerators <= 2.4*10^13.

   Proof.  [isectZ] is the same algorithm over Z; [isectZ_ok] proves
   intersect_spec of it (crossing case: [param], the point is
   A + tn/den (B - A) and lies on a segment iff 0 <= tn <= den; collinear
   case: [line_seg], on a common line a segment is the lexicographic
   interval of its ends; degenerate and parallel cases directly), and
   [isect_m_repr] proves that the machine function computes it word for
   word (Sint63.to_Z_add/sub/mul under the bounds of valid_input). *)

From Segmentintersection.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith Lia Bool Uint63.
From Stdlib Require Sint63.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* Geometry over Z                                                      *)
(* ------------------------------------------------------------------ *)

(* rational point P = (px/d, py/d) lies on the line through (ax,ay) of
   direction (rx,ry) (for rx = ry = 0 : no constraint) *)
Definition col (ax ay rx ry px py d : Z) : Prop :=
  rx * (py - ay * d) = ry * (px - ax * d).

Lemma on_seg_col : forall ax ay bx by_ px py d,
  on_seg ax ay bx by_ px py d <->
  col ax ay (bx - ax) (by_ - ay) px py d /\
  Z.min ax bx * d <= px <= Z.max ax bx * d /\
  Z.min ay by_ * d <= py <= Z.max ay by_ * d.
Proof. intros. unfold on_seg, col. tauto. Qed.

Lemma on_seg_swap : forall ax ay bx by_ px py d,
  on_seg ax ay bx by_ px py d <-> on_seg bx by_ ax ay px py d.
Proof.
  intros. unfold on_seg. rewrite (Z.min_comm ax), (Z.max_comm ax),
    (Z.min_comm ay), (Z.max_comm ay).
  split; intros [H1 H2]; split; auto; lia.
Qed.

Lemma on_seg_pt : forall ax ay px py d, 0 < d ->
  on_seg ax ay ax ay px py d <-> px = ax * d /\ py = ay * d.
Proof.
  intros. unfold on_seg. rewrite !Z.min_id, !Z.max_id. lia.
Qed.

Lemma on_seg_scale : forall ax ay bx by_ cx cy d, 0 < d ->
  on_seg ax ay bx by_ (cx * d) (cy * d) d <-> on_seg ax ay bx by_ cx cy 1.
Proof.
  intros. unfold on_seg. rewrite !Z.mul_1_r.
  assert (E : (bx - ax) * (cy * d - ay * d) = (by_ - ay) * (cx * d - ax * d)
              <-> (bx - ax) * (cy - ay) = (by_ - ay) * (cx - ax)).
  { replace ((bx - ax) * (cy * d - ay * d)) with (((bx - ax) * (cy - ay)) * d) by ring.
    replace ((by_ - ay) * (cx * d - ax * d)) with (((by_ - ay) * (cx - ax)) * d) by ring.
    split; intros H'; [apply Z.mul_cancel_r in H'; lia | rewrite H'; reflexivity]. }
  rewrite E.
  rewrite <- !Z.mul_le_mono_pos_r by lia. tauto.
Qed.

(* two directions parallel to a nonzero one are parallel *)
Lemma par_trans : forall ax ay bx by_ cx cy,
  (ax <> 0 \/ ay <> 0) ->
  bx * ay = by_ * ax -> ax * cy = ay * cx -> bx * cy = by_ * cx.
Proof.
  intros ax ay bx by_ cx cy Ha H1 H2.
  assert (Ex : ax * (bx * cy - by_ * cx) = bx * (ax * cy - ay * cx) + cx * (ay * bx - ax * by_)) by ring.
  assert (Ey : ay * (bx * cy - by_ * cx) = by_ * (ax * cy - ay * cx) + cy * (ay * bx - ax * by_)) by ring.
  replace (ax * cy - ay * cx) with 0 in Ex, Ey by lia.
  replace (ay * bx - ax * by_) with 0 in Ex, Ey by lia.
  rewrite Z.mul_0_r, Z.add_0_l, Z.mul_0_r in Ex, Ey.
  destruct Ha as [Ha | Ha].
  - apply Z.mul_eq_0 in Ex. lia.
  - apply Z.mul_eq_0 in Ey. lia.
Qed.

(* lexicographic order: on integer points (bool), integer vs rational *)
Definition lexle (ux uy vx vy : Z) : bool := (ux <? vx) || ((ux =? vx) && (uy <=? vy)).
Definition lexlt (ux uy vx vy : Z) : bool := (ux <? vx) || ((ux =? vx) && (uy <? vy)).
Definition le_ip (ux uy px py d : Z) : Prop := ux * d < px \/ (ux * d = px /\ uy * d <= py).
Definition le_pi (px py d vx vy : Z) : Prop := px < vx * d \/ (px = vx * d /\ py <= vy * d).

Lemma lexle_iff : forall ux uy vx vy,
  lexle ux uy vx vy = true <-> ux < vx \/ (ux = vx /\ uy <= vy).
Proof.
  intros. unfold lexle. rewrite orb_true_iff, andb_true_iff, Z.ltb_lt, Z.eqb_eq, Z.leb_le.
  tauto.
Qed.

Lemma lexlt_iff : forall ux uy vx vy,
  lexlt ux uy vx vy = true <-> ux < vx \/ (ux = vx /\ uy < vy).
Proof.
  intros. unfold lexlt. rewrite orb_true_iff, andb_true_iff, Z.ltb_lt, Z.eqb_eq, Z.ltb_lt.
  tauto.
Qed.

Lemma ycase : forall a b X Y d, 0 < a -> 0 < d -> a * Y = b * X -> 0 <= X <= a * d ->
  (0 <= b -> 0 <= Y <= b * d) /\ (b < 0 -> b * d <= Y <= 0).
Proof.
  intros a b X Y d Ha Hd HE HX. split; intros Hb; split.
  - nia.
  - assert (a * Y <= a * (b * d)) by nia. nia.
  - assert (a * (b * d) <= a * Y) by nia. nia.
  - nia.
Qed.

Lemma seg_lex : forall ux uy vx vy px py d, 0 < d ->
  lexle ux uy vx vy = true ->
  col ux uy (vx - ux) (vy - uy) px py d ->
  ((Z.min ux vx * d <= px <= Z.max ux vx * d /\ Z.min uy vy * d <= py <= Z.max uy vy * d)
   <-> le_ip ux uy px py d /\ le_pi px py d vx vy).
Proof.
  intros ux uy vx vy px py d Hd Hl Hc. apply lexle_iff in Hl. unfold col in Hc.
  unfold le_ip, le_pi.
  remember (px - ux * d) as X. remember (py - uy * d) as Y.
  assert (Ep : px = ux * d + X) by lia. assert (Eq : py = uy * d + Y) by lia.
  subst px py. clear HeqX HeqY.
  destruct Hl as [Hl | [-> Hl]].
  - rewrite Z.min_l, Z.max_r by lia.
    remember (vx - ux) as a. remember (vy - uy) as b.
    assert (Ev : vx = ux + a) by lia. assert (Ew : vy = uy + b) by lia.
    subst vx vy. clear Heqa Heqb.
    split.
    + intros [[H1 H2] [H3 H4]]. split.
      * destruct (Z.eq_dec X 0) as [->|HX]; [right|left; lia].
        rewrite Z.mul_0_r in Hc. assert (Y = 0) by nia. lia.
      * destruct (Z.eq_dec X (a * d)) as [->|HX]; [right|left; nia].
        assert (Y = b * d).
        { assert (a * Y = a * (b * d)) by (rewrite Hc; ring).
          apply Z.mul_cancel_l in H; lia. }
        nia.
    + intros [H1 H2].
      assert (HX : 0 <= X <= a * d).
      { split.
        - destruct H1 as [H1 | [H1 _]]; lia.
        - destruct H2 as [H2 | [H2 _]]; nia. }
      destruct (ycase a b X Y d ltac:(lia) Hd Hc HX) as [Hp Hn].
      split; [nia|].
      destruct (Z_le_gt_dec 0 b) as [Hb | Hb].
      * rewrite Z.min_l, Z.max_r by lia. specialize (Hp Hb). nia.
      * rewrite Z.min_r, Z.max_l by lia. specialize (Hn ltac:(lia)). nia.
  - rewrite Z.min_id, Z.max_id, Z.min_l, Z.max_r by lia.
    destruct (Z.eq_dec uy vy) as [<-|Hne].
    + rewrite Z.sub_diag, Z.mul_0_l in Hc. lia.
    + assert (X = 0) by (rewrite Z.sub_diag, Z.mul_0_l in Hc; symmetry in Hc;
                         apply Z.mul_eq_0 in Hc; lia).
      subst X. nia.
Qed.

Lemma line_col : forall ax ay rx ry ux uy vx vy px py d,
  (rx <> 0 \/ ry <> 0) ->
  col ax ay rx ry ux uy 1 -> col ax ay rx ry vx vy 1 ->
  (ux <> vx \/ uy <> vy) ->
  (col ux uy (vx - ux) (vy - uy) px py d <-> col ax ay rx ry px py d).
Proof.
  intros ax ay rx ry ux uy vx vy px py d Hr Hu Hv Hne. unfold col in *.
  rewrite !Z.mul_1_r in Hu, Hv.
  assert (Hp : rx * (vy - uy) = ry * (vx - ux)) by lia.
  assert (EA : rx * (py - ay * d) - ry * (px - ax * d)
               = rx * (py - uy * d) - ry * (px - ux * d)
                 + d * (rx * (uy - ay) - ry * (ux - ax))) by ring.
  rewrite Hu, Z.sub_diag, Z.mul_0_r, Z.add_0_r in EA.
  split; intros H.
  - assert (rx * (py - uy * d) = ry * (px - ux * d)).
    { apply (par_trans (vx - ux) (vy - uy)); [lia | lia | exact H]. }
    lia.
  - apply (par_trans rx ry); [exact Hr | lia | lia].
Qed.

Lemma col_scale : forall ax ay rx ry ux uy d, 0 < d ->
  col ax ay rx ry ux uy 1 -> col ax ay rx ry (ux * d) (uy * d) d.
Proof.
  unfold col. intros ax ay rx ry ux uy d Hd H. rewrite !Z.mul_1_r in H.
  replace (rx * (uy * d - ay * d)) with ((rx * (uy - ay)) * d) by ring.
  rewrite H. ring.
Qed.

Lemma line_seg : forall ax ay rx ry ux uy vx vy px py d, 0 < d ->
  (rx <> 0 \/ ry <> 0) ->
  col ax ay rx ry ux uy 1 -> col ax ay rx ry vx vy 1 ->
  lexlt ux uy vx vy = true ->
  (on_seg ux uy vx vy px py d <->
   col ax ay rx ry px py d /\ le_ip ux uy px py d /\ le_pi px py d vx vy).
Proof.
  intros ax ay rx ry ux uy vx vy px py d Hd Hr Hu Hv Hlt.
  assert (Hle : lexle ux uy vx vy = true)
    by (apply lexle_iff; apply lexlt_iff in Hlt; lia).
  assert (Hne : ux <> vx \/ uy <> vy) by (apply lexlt_iff in Hlt; lia).
  rewrite on_seg_col.
  split.
  - intros [Hc Hb]. split; [exact (proj1 (line_col _ _ _ _ _ _ _ _ _ _ _ Hr Hu Hv Hne) Hc)|].
    exact (proj1 (seg_lex _ _ _ _ _ _ _ Hd Hle Hc) Hb).
  - intros [Hc Hb].
    pose proof (proj2 (line_col _ _ _ _ _ _ _ _ px py d Hr Hu Hv Hne) Hc) as Hc'.
    split; [exact Hc'|].
    exact (proj2 (seg_lex _ _ _ _ _ _ _ Hd Hle Hc') Hb).
Qed.

Lemma le_ip_trans : forall ux uy vx vy px py d, 0 < d ->
  lexle ux uy vx vy = true -> le_ip vx vy px py d -> le_ip ux uy px py d.
Proof. unfold le_ip. intros * Hd Hl H. apply lexle_iff in Hl. nia. Qed.

Lemma le_pi_trans : forall ux uy vx vy px py d, 0 < d ->
  lexle ux uy vx vy = true -> le_pi px py d ux uy -> le_pi px py d vx vy.
Proof. unfold le_pi. intros * Hd Hl H. apply lexle_iff in Hl. nia. Qed.

Lemma le_ipi : forall ux uy vx vy px py d, 0 < d ->
  le_ip ux uy px py d -> le_pi px py d vx vy -> lexle ux uy vx vy = true.
Proof. unfold le_ip, le_pi. intros * Hd H1 H2. apply lexle_iff. nia. Qed.

Lemma le_antisym : forall ux uy px py d, 0 < d ->
  le_ip ux uy px py d -> le_pi px py d ux uy -> px = ux * d /\ py = uy * d.
Proof. unfold le_ip, le_pi. intros. lia. Qed.

Lemma le_refl : forall ux uy d, le_ip ux uy (ux * d) (uy * d) d /\ le_pi (ux * d) (uy * d) d ux uy.
Proof. unfold le_ip, le_pi. intros. lia. Qed.

Lemma lexle_total : forall ux uy vx vy, lexle ux uy vx vy = false -> lexle vx vy ux uy = true.
Proof.
  intros. apply lexle_iff. destruct (lexle ux uy vx vy) eqn:E; [discriminate|].
  rewrite <- not_true_iff_false, lexle_iff in E. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The collinear case over Z                                            *)
(* ------------------------------------------------------------------ *)

(* the intersection [lo, hi] of two collinear segments, lexicographic ends *)
Definition finishZ (lox loy hix hiy : Z) : inter Z :=
  if lexlt lox loy hix hiy then Segment lox loy hix hiy
  else if (lox =? hix) && (loy =? hiy) then Point lox loy 1
  else Empty.

(* [p1,p2] /\ [p3,p4], each sorted: max of the lows, min of the highs *)
Definition coll2Z (p1x p1y p2x p2y p3x p3y p4x p4y : Z) : inter Z :=
  if lexle p1x p1y p3x p3y then
    (if lexle p2x p2y p4x p4y then finishZ p3x p3y p2x p2y else finishZ p3x p3y p4x p4y)
  else
    (if lexle p2x p2y p4x p4y then finishZ p1x p1y p2x p2y else finishZ p1x p1y p4x p4y).

Definition coll1Z (p1x p1y p2x p2y x3 y3 x4 y4 : Z) : inter Z :=
  if lexle x3 y3 x4 y4 then coll2Z p1x p1y p2x p2y x3 y3 x4 y4
  else coll2Z p1x p1y p2x p2y x4 y4 x3 y3.

Definition collZ (x1 y1 x2 y2 x3 y3 x4 y4 : Z) : inter Z :=
  if lexle x1 y1 x2 y2 then coll1Z x1 y1 x2 y2 x3 y3 x4 y4
  else coll1Z x2 y2 x1 y1 x3 y3 x4 y4.

Section Line.
  Variables ax ay rx ry : Z.
  Hypothesis Hr : rx <> 0 \/ ry <> 0.
  Let on_line ux uy := col ax ay rx ry ux uy 1.

  Lemma finish_ok : forall lox loy hix hiy,
    on_line lox loy -> on_line hix hiy ->
    well_formed (finishZ lox loy hix hiy) /\
    forall px py d, 0 < d ->
      (denotes (finishZ lox loy hix hiy) px py d <->
       col ax ay rx ry px py d /\ le_ip lox loy px py d /\ le_pi px py d hix hiy).
  Proof.
    intros lox loy hix hiy Hlo Hhi. unfold finishZ.
    destruct (lexlt lox loy hix hiy) eqn:Elt.
    - split; [simpl; apply lexlt_iff in Elt; lia|].
      intros px py d Hd. simpl. exact (line_seg _ _ _ _ _ _ _ _ _ _ _ Hd Hr Hlo Hhi Elt).
    - destruct ((lox =? hix) && (loy =? hiy)) eqn:Eeq.
      + apply andb_true_iff in Eeq. rewrite !Z.eqb_eq in Eeq. destruct Eeq as [<- <-].
        split; [simpl; lia|].
        intros px py d Hd. simpl. split.
        * intros [E1 E2]. rewrite Z.mul_1_r in E1, E2. subst px py.
          split; [exact (col_scale _ _ _ _ _ _ _ Hd Hlo)|]. apply le_refl.
        * intros [_ [H1 H2]]. pose proof (le_antisym _ _ _ _ _ Hd H1 H2). lia.
      + split; [exact I|].
        intros px py d Hd. simpl. split; [tauto|].
        intros [_ [H1 H2]]. pose proof (le_ipi _ _ _ _ _ _ _ Hd H1 H2) as Hle.
        apply lexle_iff in Hle.
        rewrite <- not_true_iff_false, lexlt_iff in Elt.
        rewrite <- not_true_iff_false, andb_true_iff, !Z.eqb_eq in Eeq. lia.
  Qed.

  Lemma coll2_ok : forall p1x p1y p2x p2y p3x p3y p4x p4y,
    on_line p1x p1y -> on_line p2x p2y -> on_line p3x p3y -> on_line p4x p4y ->
    lexlt p1x p1y p2x p2y = true -> lexlt p3x p3y p4x p4y = true ->
    well_formed (coll2Z p1x p1y p2x p2y p3x p3y p4x p4y) /\
    forall px py d, 0 < d ->
      (denotes (coll2Z p1x p1y p2x p2y p3x p3y p4x p4y) px py d <->
       on_seg p1x p1y p2x p2y px py d /\ on_seg p3x p3y p4x p4y px py d).
  Proof.
    intros p1x p1y p2x p2y p3x p3y p4x p4y H1 H2 H3 H4 H12 H34.
    assert (G : forall lox loy hix hiy, on_line lox loy -> on_line hix hiy ->
      (forall px py d, 0 < d ->
         (le_ip lox loy px py d <-> le_ip p1x p1y px py d /\ le_ip p3x p3y px py d)) ->
      (forall px py d, 0 < d ->
         (le_pi px py d hix hiy <-> le_pi px py d p2x p2y /\ le_pi px py d p4x p4y)) ->
      well_formed (finishZ lox loy hix hiy) /\
      forall px py d, 0 < d ->
        (denotes (finishZ lox loy hix hiy) px py d <->
         on_seg p1x p1y p2x p2y px py d /\ on_seg p3x p3y p4x p4y px py d)).
    { intros lox loy hix hiy Hlo Hhi Elo Ehi.
      destruct (finish_ok lox loy hix hiy Hlo Hhi) as [Hw Hd]. split; [exact Hw|].
      intros px py d Hd0. rewrite Hd by exact Hd0.
      rewrite (line_seg _ _ _ _ _ _ _ _ px py d Hd0 Hr H1 H2 H12).
      rewrite (line_seg _ _ _ _ _ _ _ _ px py d Hd0 Hr H3 H4 H34).
      rewrite (Elo px py d Hd0), (Ehi px py d Hd0). tauto. }
    unfold coll2Z.
    destruct (lexle p1x p1y p3x p3y) eqn:E13;
    [pose proof (fun px py d Hd => conj (fun H : le_ip p3x p3y px py d =>
        conj (le_ip_trans _ _ _ _ _ _ d Hd E13 H) H)
        (fun H : le_ip p1x p1y px py d /\ le_ip p3x p3y px py d => proj2 H)) as L
    |pose proof (lexle_total _ _ _ _ E13) as E31;
     pose proof (fun px py d Hd => conj (fun H : le_ip p1x p1y px py d =>
        conj H (le_ip_trans _ _ _ _ _ _ d Hd E31 H))
        (fun H : le_ip p1x p1y px py d /\ le_ip p3x p3y px py d => proj1 H)) as L];
    (destruct (lexle p2x p2y p4x p4y) eqn:E24;
    [pose proof (fun px py d Hd => conj (fun H : le_pi px py d p2x p2y =>
        conj H (le_pi_trans _ _ _ _ _ _ d Hd E24 H))
        (fun H : le_pi px py d p2x p2y /\ le_pi px py d p4x p4y => proj1 H)) as R
    |pose proof (lexle_total _ _ _ _ E24) as E42;
     pose proof (fun px py d Hd => conj (fun H : le_pi px py d p4x p4y =>
        conj (le_pi_trans _ _ _ _ _ _ d Hd E42 H) H)
        (fun H : le_pi px py d p2x p2y /\ le_pi px py d p4x p4y => proj2 H)) as R]);
    apply G; assumption.
  Qed.

End Line.

Lemma lexlt_of_le : forall ux uy vx vy, lexle ux uy vx vy = true ->
  (ux <> vx \/ uy <> vy) -> lexlt ux uy vx vy = true.
Proof. intros * H Hn. apply lexle_iff in H. apply lexlt_iff. lia. Qed.

Lemma lexlt_of_nle : forall ux uy vx vy, lexle ux uy vx vy = false ->
  lexlt vx vy ux uy = true.
Proof.
  intros * H. apply lexlt_iff.
  rewrite <- not_true_iff_false, lexle_iff in H. lia.
Qed.

Lemma collZ_ok : forall x1 y1 x2 y2 x3 y3 x4 y4,
  let rx := x2 - x1 in let ry := y2 - y1 in
  (rx <> 0 \/ ry <> 0) -> (x4 - x3 <> 0 \/ y4 - y3 <> 0) ->
  col x1 y1 rx ry x3 y3 1 -> col x1 y1 rx ry x4 y4 1 ->
  well_formed (collZ x1 y1 x2 y2 x3 y3 x4 y4) /\
  forall px py d, 0 < d ->
    (denotes (collZ x1 y1 x2 y2 x3 y3 x4 y4) px py d <->
     on_seg x1 y1 x2 y2 px py d /\ on_seg x3 y3 x4 y4 px py d).
Proof.
  intros x1 y1 x2 y2 x3 y3 x4 y4 rx ry Hr Hs H3 H4.
  assert (H1 : col x1 y1 rx ry x1 y1 1) by (unfold col; ring).
  assert (H2 : col x1 y1 rx ry x2 y2 1) by (unfold col, rx, ry; ring).
  unfold collZ, coll1Z.
  destruct (lexle x1 y1 x2 y2) eqn:E12;
  [pose proof (lexlt_of_le _ _ _ _ E12 ltac:(lia)) as L12
  |pose proof (lexlt_of_nle _ _ _ _ E12) as L12];
  (destruct (lexle x3 y3 x4 y4) eqn:E34;
  [pose proof (lexlt_of_le _ _ _ _ E34 ltac:(lia)) as L34
  |pose proof (lexlt_of_nle _ _ _ _ E34) as L34]);
  (edestruct (coll2_ok x1 y1 rx ry Hr) as [Hw Hd];
   [| | | | exact L12 | exact L34 | ]; try eassumption);
  (split; [exact Hw|]);
  intros px py d Hd0; rewrite (Hd px py d Hd0);
  rewrite ?(on_seg_swap x2 y2 x1 y1), ?(on_seg_swap x4 y4 x3 y3); tauto.
Qed.

(* ------------------------------------------------------------------ *)
(* The crossing case over Z                                             *)
(* ------------------------------------------------------------------ *)

Lemma coord_fwd : forall a b w k d m, 0 < k -> 0 < d ->
  w * k = d * m * (b - a) -> 0 <= m <= k ->
  Z.min a b * d <= a * d + w <= Z.max a b * d.
Proof.
  intros a b w k d m Hk Hd He Hm.
  replace (d * m * (b - a)) with ((b - a) * d * m) in He by ring.
  destruct (Z_le_gt_dec a b).
  - rewrite Z.min_l, Z.max_r by lia.
    assert (Hbd : 0 <= (b - a) * d) by nia.
    assert (H1 : 0 <= w * k) by (rewrite He; apply Z.mul_nonneg_nonneg; lia).
    assert (H2 : w * k <= (b - a) * d * k)
      by (rewrite He; apply Z.mul_le_mono_nonneg_l; lia).
    assert (0 <= w) by nia.
    assert (w <= (b - a) * d) by (apply (Z.mul_le_mono_pos_r _ _ k); lia).
    lia.
  - rewrite Z.min_r, Z.max_l by lia.
    assert (Hbd : (b - a) * d <= 0) by nia.
    assert (H1 : w * k <= 0) by (rewrite He; apply Z.mul_nonpos_nonneg; lia).
    assert (H2 : (b - a) * d * k <= w * k)
      by (rewrite He; apply Z.mul_le_mono_nonpos_l; lia).
    assert (w <= 0) by nia.
    assert ((b - a) * d <= w) by (apply (Z.mul_le_mono_pos_r _ _ k); lia).
    lia.
Qed.

Lemma coord_bwd : forall a b w k d m, 0 < k -> 0 < d -> a <> b ->
  w * k = d * m * (b - a) ->
  Z.min a b * d <= a * d + w <= Z.max a b * d -> 0 <= m <= k.
Proof.
  intros a b w k d m Hk Hd Hab He Hb.
  replace (d * m * (b - a)) with ((b - a) * d * m) in He by ring.
  destruct (Z_le_gt_dec a b).
  - rewrite Z.min_l, Z.max_r in Hb by lia.
    assert (Hbd : 0 < (b - a) * d) by nia.
    assert (H1 : 0 <= w * k) by nia.
    assert (H2 : w * k <= (b - a) * d * k)
      by (apply Z.mul_le_mono_nonneg_r; lia).
    rewrite He in H1, H2. split.
    + nia.
    + apply (Z.mul_le_mono_pos_l _ _ ((b - a) * d)); lia.
  - rewrite Z.min_r, Z.max_l in Hb by lia.
    assert (Hbd : (b - a) * d < 0) by nia.
    assert (H1 : w * k <= 0) by nia.
    assert (H2 : (b - a) * d * k <= w * k)
      by (apply Z.mul_le_mono_nonneg_r; lia).
    rewrite He in H1, H2. split.
    + nia.
    + assert (((a - b) * d) * m <= ((a - b) * d) * k) by nia.
      apply (Z.mul_le_mono_pos_l _ _ ((a - b) * d)); nia.
Qed.

Lemma param : forall ax ay bx by_ px py d k m, 0 < d -> 0 < k ->
  (bx - ax <> 0 \/ by_ - ay <> 0) ->
  (px - ax * d) * k = d * m * (bx - ax) ->
  (py - ay * d) * k = d * m * (by_ - ay) ->
  (on_seg ax ay bx by_ px py d <-> 0 <= m <= k).
Proof.
  intros ax ay bx by_ px py d k m Hd Hk Hr Ex Ey.
  unfold on_seg.
  replace px with (ax * d + (px - ax * d)) by ring.
  replace py with (ay * d + (py - ay * d)) by ring.
  split.
  - intros [_ [Bx By]]. destruct Hr as [Hr | Hr].
    + exact (coord_bwd ax bx _ k d m Hk Hd ltac:(lia) Ex Bx).
    + exact (coord_bwd ay by_ _ k d m Hk Hd ltac:(lia) Ey By).
  - intros Hm. split; [|split].
    + apply (Z.mul_cancel_r _ _ k); [lia|].
      replace (ay * d + (py - ay * d) - ay * d) with (py - ay * d) by ring.
      replace (ax * d + (px - ax * d) - ax * d) with (px - ax * d) by ring.
      replace ((bx - ax) * (py - ay * d) * k) with ((bx - ax) * ((py - ay * d) * k)) by ring.
      replace ((by_ - ay) * (px - ax * d) * k) with ((by_ - ay) * ((px - ax * d) * k)) by ring.
      rewrite Ex, Ey. ring.
    + exact (coord_fwd ax bx _ k d m Hk Hd Ex Hm).
    + exact (coord_fwd ay by_ _ k d m Hk Hd Ey Hm).
Qed.

Definition cross_finZ (x1 y1 rx ry den tn un : Z) : inter Z :=
  if (0 <=? tn) && (tn <=? den) && (0 <=? un) && (un <=? den)
  then Point (x1 * den + tn * rx) (y1 * den + tn * ry) den
  else Empty.

Definition crossingZ (x1 y1 rx ry den tn un : Z) : inter Z :=
  if den <? 0 then cross_finZ x1 y1 rx ry (- den) (- tn) (- un)
  else cross_finZ x1 y1 rx ry den tn un.

Lemma cross_fin_ok : forall x1 y1 x2 y2 x3 y3 x4 y4 sg den tn un,
  den = sg * ((x2 - x1) * (y4 - y3) - (y2 - y1) * (x4 - x3)) ->
  tn = sg * ((x3 - x1) * (y4 - y3) - (y3 - y1) * (x4 - x3)) ->
  un = sg * ((x3 - x1) * (y2 - y1) - (y3 - y1) * (x2 - x1)) ->
  0 < den ->
  well_formed (cross_finZ x1 y1 (x2 - x1) (y2 - y1) den tn un) /\
  forall px py d, 0 < d ->
    (denotes (cross_finZ x1 y1 (x2 - x1) (y2 - y1) den tn un) px py d <->
     on_seg x1 y1 x2 y2 px py d /\ on_seg x3 y3 x4 y4 px py d).
Proof.
  intros x1 y1 x2 y2 x3 y3 x4 y4 sg den tn un Hden Htn Hun Hpos.
  assert (Hr : x2 - x1 <> 0 \/ y2 - y1 <> 0).
  { destruct (Z.eq_dec (x2 - x1) 0) as [E1|]; [|lia].
    destruct (Z.eq_dec (y2 - y1) 0) as [E2|]; [|lia].
    rewrite E1, E2 in Hden. lia. }
  assert (Hs : x4 - x3 <> 0 \/ y4 - y3 <> 0).
  { destruct (Z.eq_dec (x4 - x3) 0) as [E1|]; [|lia].
    destruct (Z.eq_dec (y4 - y3) 0) as [E2|]; [|lia].
    rewrite E1, E2 in Hden. lia. }
  (* E : the point (px/d,py/d) is A + tn/den (B - A) *)
  assert (ES1 : forall px py d, 0 < d ->
            (px - x1 * d) * den = d * tn * (x2 - x1) ->
            (py - y1 * d) * den = d * tn * (y2 - y1) ->
            (on_seg x1 y1 x2 y2 px py d <-> 0 <= tn <= den)).
  { intros px py d Hd Ex Ey. exact (param _ _ _ _ _ _ _ _ _ Hd Hpos Hr Ex Ey). }
  assert (ES2 : forall px py d, 0 < d ->
            (px - x1 * d) * den = d * tn * (x2 - x1) ->
            (py - y1 * d) * den = d * tn * (y2 - y1) ->
            (on_seg x3 y3 x4 y4 px py d <-> 0 <= un <= den)).
  { intros px py d Hd Ex Ey. apply (param _ _ _ _ _ _ _ _ _ Hd Hpos Hs).
    - replace ((px - x3 * d) * den) with ((px - x1 * d) * den - d * (den * (x3 - x1))) by ring.
      rewrite Ex. subst den tn un. ring.
    - replace ((py - y3 * d) * den) with ((py - y1 * d) * den - d * (den * (y3 - y1))) by ring.
      rewrite Ey. subst den tn un. ring. }
  assert (EB : forall px py d, 0 < d ->
            on_seg x1 y1 x2 y2 px py d -> on_seg x3 y3 x4 y4 px py d ->
            (px - x1 * d) * den = d * tn * (x2 - x1) /\
            (py - y1 * d) * den = d * tn * (y2 - y1)).
  { intros px py d Hd [C1 _] [C2 _].
    assert (Z1 : (px - x3 * d) * (y4 - y3) - (py - y3 * d) * (x4 - x3) = 0) by lia.
    assert (Z2 : (x2 - x1) * (py - y1 * d) - (y2 - y1) * (px - x1 * d) = 0) by lia.
    split.
    - assert (Hx : (px - x1 * d) * den =
                   sg * (((px - x3 * d) * (y4 - y3) - (py - y3 * d) * (x4 - x3)) * (x2 - x1)
                         + d * ((x3 - x1) * (y4 - y3) - (y3 - y1) * (x4 - x3)) * (x2 - x1)
                         + ((x2 - x1) * (py - y1 * d) - (y2 - y1) * (px - x1 * d)) * (x4 - x3)))
        by (subst den; ring).
      rewrite Z1, Z2 in Hx. rewrite Hx, Htn. ring.
    - assert (Hy : (py - y1 * d) * den =
                   sg * (((px - x3 * d) * (y4 - y3) - (py - y3 * d) * (x4 - x3)) * (y2 - y1)
                         + d * ((x3 - x1) * (y4 - y3) - (y3 - y1) * (x4 - x3)) * (y2 - y1)
                         + ((x2 - x1) * (py - y1 * d) - (y2 - y1) * (px - x1 * d)) * (y4 - y3)))
        by (subst den; ring).
      rewrite Z1, Z2 in Hy. rewrite Hy, Htn. ring. }
  unfold cross_finZ.
  destruct ((0 <=? tn) && (tn <=? den) && (0 <=? un) && (un <=? den)) eqn:Ec.
  - rewrite !andb_true_iff, !Z.leb_le in Ec.
    split; [simpl; lia|].
    intros px py d Hd. simpl. split.
    + intros [Ex Ey].
      assert (Ex' : (px - x1 * d) * den = d * tn * (x2 - x1)) by lia.
      assert (Ey' : (py - y1 * d) * den = d * tn * (y2 - y1)) by lia.
      rewrite (ES1 _ _ _ Hd Ex' Ey'), (ES2 _ _ _ Hd Ex' Ey'). lia.
    + intros [S1 S2]. destruct (EB _ _ _ Hd S1 S2) as [Ex Ey]. lia.
  - split; [exact I|].
    intros px py d Hd. simpl. split; [tauto|].
    intros [S1 S2]. destruct (EB _ _ _ Hd S1 S2) as [Ex Ey].
    pose proof (proj1 (ES1 _ _ _ Hd Ex Ey) S1).
    pose proof (proj1 (ES2 _ _ _ Hd Ex Ey) S2).
    rewrite <- not_true_iff_false, !andb_true_iff, !Z.leb_le in Ec. lia.
Qed.

Lemma crossingZ_ok : forall x1 y1 x2 y2 x3 y3 x4 y4,
  let den := (x2 - x1) * (y4 - y3) - (y2 - y1) * (x4 - x3) in
  den <> 0 ->
  well_formed (crossingZ x1 y1 (x2 - x1) (y2 - y1) den
                 ((x3 - x1) * (y4 - y3) - (y3 - y1) * (x4 - x3))
                 ((x3 - x1) * (y2 - y1) - (y3 - y1) * (x2 - x1))) /\
  forall px py d, 0 < d ->
    (denotes (crossingZ x1 y1 (x2 - x1) (y2 - y1) den
                 ((x3 - x1) * (y4 - y3) - (y3 - y1) * (x4 - x3))
                 ((x3 - x1) * (y2 - y1) - (y3 - y1) * (x2 - x1))) px py d <->
     on_seg x1 y1 x2 y2 px py d /\ on_seg x3 y3 x4 y4 px py d).
Proof.
  intros x1 y1 x2 y2 x3 y3 x4 y4 den Hden. unfold crossingZ.
  destruct (den <? 0) eqn:E.
  - apply Z.ltb_lt in E.
    apply (cross_fin_ok x1 y1 x2 y2 x3 y3 x4 y4 (-1)); unfold den in *; lia.
  - apply Z.ltb_ge in E.
    apply (cross_fin_ok x1 y1 x2 y2 x3 y3 x4 y4 1); unfold den in *; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Degenerate and parallel cases over Z                                 *)
(* ------------------------------------------------------------------ *)

(* on_seg with d = 1, as a boolean *)
Definition onsegbZ (ax ay bx by_ px py : Z) : bool :=
  ((bx - ax) * (py - ay) =? (by_ - ay) * (px - ax))
  && (((ax <=? px) && (px <=? bx)) || ((bx <=? px) && (px <=? ax)))
  && (((ay <=? py) && (py <=? by_)) || ((by_ <=? py) && (py <=? ay))).

Lemma onsegbZ_iff : forall ax ay bx by_ px py,
  onsegbZ ax ay bx by_ px py = true <-> on_seg ax ay bx by_ px py 1.
Proof.
  intros. unfold onsegbZ, on_seg.
  rewrite !andb_true_iff, !orb_true_iff, !andb_true_iff, !Z.eqb_eq, !Z.leb_le.
  rewrite !Z.mul_1_r. lia.
Qed.

Lemma pointA_ok : forall x1 y1 x3 y3 x4 y4,
  well_formed (if onsegbZ x3 y3 x4 y4 x1 y1 then Point x1 y1 1 else Empty) /\
  forall px py d, 0 < d ->
    (denotes (if onsegbZ x3 y3 x4 y4 x1 y1 then Point x1 y1 1 else Empty) px py d <->
     on_seg x1 y1 x1 y1 px py d /\ on_seg x3 y3 x4 y4 px py d).
Proof.
  intros. destruct (onsegbZ x3 y3 x4 y4 x1 y1) eqn:E.
  - apply onsegbZ_iff in E. split; [simpl; lia|].
    intros px py d Hd. simpl. rewrite (on_seg_pt _ _ _ _ _ Hd). split.
    + intros [E1 E2]. rewrite Z.mul_1_r in E1, E2. subst px py. split; [lia|].
      apply on_seg_scale; assumption.
    + intros [[-> ->] _]. lia.
  - split; [exact I|]. intros px py d Hd. simpl. split; [tauto|].
    rewrite (on_seg_pt _ _ _ _ _ Hd). intros [[-> ->] H].
    apply (on_seg_scale _ _ _ _ _ _ _ Hd), onsegbZ_iff in H. congruence.
Qed.

Lemma parallel_empty : forall x1 y1 x2 y2 x3 y3 x4 y4 px py d, 0 < d ->
  (x4 - x3 <> 0 \/ y4 - y3 <> 0) ->
  (x2 - x1) * (y4 - y3) - (y2 - y1) * (x4 - x3) = 0 ->
  (x3 - x1) * (y2 - y1) - (y3 - y1) * (x2 - x1) <> 0 ->
  ~ (on_seg x1 y1 x2 y2 px py d /\ on_seg x3 y3 x4 y4 px py d).
Proof.
  intros x1 y1 x2 y2 x3 y3 x4 y4 px py d Hd Hs Hden Hun [[C1 _] [C2 _]].
  assert (C : (x2 - x1) * (py - y3 * d) = (y2 - y1) * (px - x3 * d)).
  { apply (par_trans (x4 - x3) (y4 - y3)); [exact Hs | lia | exact C2]. }
  assert (E : d * ((x3 - x1) * (y2 - y1) - (y3 - y1) * (x2 - x1)) = 0).
  { replace (d * ((x3 - x1) * (y2 - y1) - (y3 - y1) * (x2 - x1)))
      with (((x2 - x1) * (py - y3 * d) - (y2 - y1) * (px - x3 * d))
            - ((x2 - x1) * (py - y1 * d) - (y2 - y1) * (px - x1 * d))) by ring.
    lia. }
  apply Z.mul_eq_0 in E. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The whole algorithm over Z                                           *)
(* ------------------------------------------------------------------ *)

Definition isectZ (x1 y1 x2 y2 x3 y3 x4 y4 : Z) : inter Z :=
  let rx := x2 - x1 in let ry := y2 - y1 in
  let sx := x4 - x3 in let sy := y4 - y3 in
  let qx := x3 - x1 in let qy := y3 - y1 in
  let den := rx * sy - ry * sx in
  let un := qx * ry - qy * rx in
  if den =? 0 then
    if (rx =? 0) && (ry =? 0) then
      (if onsegbZ x3 y3 x4 y4 x1 y1 then Point x1 y1 1 else Empty)
    else if (sx =? 0) && (sy =? 0) then
      (if onsegbZ x1 y1 x2 y2 x3 y3 then Point x3 y3 1 else Empty)
    else if un =? 0 then collZ x1 y1 x2 y2 x3 y3 x4 y4
    else Empty
  else crossingZ x1 y1 rx ry den (qx * sy - qy * sx) un.

Theorem isectZ_ok : forall x1 y1 x2 y2 x3 y3 x4 y4,
  intersect_spec x1 y1 x2 y2 x3 y3 x4 y4 (isectZ x1 y1 x2 y2 x3 y3 x4 y4).
Proof.
  intros. unfold intersect_spec, isectZ. cbv zeta.
  destruct ((x2 - x1) * (y4 - y3) - (y2 - y1) * (x4 - x3) =? 0) eqn:Eden.
  2:{ apply Z.eqb_neq in Eden. exact (crossingZ_ok x1 y1 x2 y2 x3 y3 x4 y4 Eden). }
  apply Z.eqb_eq in Eden.
  destruct ((x2 - x1 =? 0) && (y2 - y1 =? 0)) eqn:Er.
  { apply andb_true_iff in Er. rewrite !Z.eqb_eq in Er.
    replace x2 with x1 by lia. replace y2 with y1 by lia. apply pointA_ok. }
  assert (Hr : x2 - x1 <> 0 \/ y2 - y1 <> 0).
  { rewrite <- not_true_iff_false, andb_true_iff, !Z.eqb_eq in Er. lia. }
  destruct ((x4 - x3 =? 0) && (y4 - y3 =? 0)) eqn:Es.
  { apply andb_true_iff in Es. rewrite !Z.eqb_eq in Es.
    replace x4 with x3 by lia. replace y4 with y3 by lia.
    destruct (pointA_ok x3 y3 x1 y1 x2 y2) as [Hw Hd]. split; [exact Hw|].
    intros px py d Hd0. rewrite (Hd px py d Hd0). tauto. }
  assert (Hs : x4 - x3 <> 0 \/ y4 - y3 <> 0).
  { rewrite <- not_true_iff_false, andb_true_iff, !Z.eqb_eq in Es. lia. }
  destruct ((x3 - x1) * (y2 - y1) - (y3 - y1) * (x2 - x1) =? 0) eqn:Eun.
  - apply Z.eqb_eq in Eun.
    apply collZ_ok; [exact Hr | exact Hs | unfold col; lia | unfold col; lia].
  - apply Z.eqb_neq in Eun. split; [exact I|].
    intros px py d Hd. simpl. split; [tauto|].
    exact (parallel_empty _ _ _ _ _ _ _ _ px py d Hd Hs Eden Eun).
Qed.

(* ------------------------------------------------------------------ *)
(* The program: the same algorithm on 63-bit words read through Sint63 *)
(* ------------------------------------------------------------------ *)

Section Machine.
  Local Open Scope uint63_scope.

  Definition lexle_m (ux uy vx vy : sint) : bool :=
    Sint63.ltb ux vx || ((ux =? vx) && Sint63.leb uy vy).
  Definition lexlt_m (ux uy vx vy : sint) : bool :=
    Sint63.ltb ux vx || ((ux =? vx) && Sint63.ltb uy vy).

  Definition finish_m (lox loy hix hiy : sint) : inter sint :=
    if lexlt_m lox loy hix hiy then Segment lox loy hix hiy
    else if (lox =? hix) && (loy =? hiy) then Point lox loy 1
    else Empty.

  Definition coll2_m (p1x p1y p2x p2y p3x p3y p4x p4y : sint) : inter sint :=
    if lexle_m p1x p1y p3x p3y then
      (if lexle_m p2x p2y p4x p4y then finish_m p3x p3y p2x p2y else finish_m p3x p3y p4x p4y)
    else
      (if lexle_m p2x p2y p4x p4y then finish_m p1x p1y p2x p2y else finish_m p1x p1y p4x p4y).

  Definition coll1_m (p1x p1y p2x p2y x3 y3 x4 y4 : sint) : inter sint :=
    if lexle_m x3 y3 x4 y4 then coll2_m p1x p1y p2x p2y x3 y3 x4 y4
    else coll2_m p1x p1y p2x p2y x4 y4 x3 y3.

  Definition coll_m (x1 y1 x2 y2 x3 y3 x4 y4 : sint) : inter sint :=
    if lexle_m x1 y1 x2 y2 then coll1_m x1 y1 x2 y2 x3 y3 x4 y4
    else coll1_m x2 y2 x1 y1 x3 y3 x4 y4.

  Definition onseg_m (ax ay bx by_ px py : sint) : bool :=
    ((bx - ax) * (py - ay) =? (by_ - ay) * (px - ax))
    && ((Sint63.leb ax px && Sint63.leb px bx) || (Sint63.leb bx px && Sint63.leb px ax))
    && ((Sint63.leb ay py && Sint63.leb py by_) || (Sint63.leb by_ py && Sint63.leb py ay)).

  Definition cross_fin_m (x1 y1 rx ry den tn un : sint) : inter sint :=
    if Sint63.leb 0 tn && Sint63.leb tn den && Sint63.leb 0 un && Sint63.leb un den
    then Point (x1 * den + tn * rx) (y1 * den + tn * ry) den
    else Empty.

  Definition crossing_m (x1 y1 rx ry den tn un : sint) : inter sint :=
    if Sint63.ltb den 0 then cross_fin_m x1 y1 rx ry (0 - den) (0 - tn) (0 - un)
    else cross_fin_m x1 y1 rx ry den tn un.

  Definition isect_m (x1 y1 x2 y2 x3 y3 x4 y4 : sint) : inter sint :=
    let rx := x2 - x1 in let ry := y2 - y1 in
    let sx := x4 - x3 in let sy := y4 - y3 in
    let qx := x3 - x1 in let qy := y3 - y1 in
    let den := rx * sy - ry * sx in
    let un := qx * ry - qy * rx in
    if den =? 0 then
      if (rx =? 0) && (ry =? 0) then
        (if onseg_m x3 y3 x4 y4 x1 y1 then Point x1 y1 1 else Empty)
      else if (sx =? 0) && (sy =? 0) then
        (if onseg_m x1 y1 x2 y2 x3 y3 then Point x3 y3 1 else Empty)
      else if un =? 0 then coll_m x1 y1 x2 y2 x3 y3 x4 y4
      else Empty
    else crossing_m x1 y1 rx ry den (qx * sy - qy * sx) un.
End Machine.

(* ------------------------------------------------------------------ *)
(* The program computes isectZ                                          *)
(* ------------------------------------------------------------------ *)

Notation sZ := Sint63.to_Z.

Lemma ltb_m : forall a b : int, Sint63.ltb a b = (sZ a <? sZ b).
Proof.
  intros a b. destruct (Sint63.ltbP a b); symmetry;
    [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma leb_m : forall a b : int, Sint63.leb a b = (sZ a <=? sZ b).
Proof.
  intros a b. destruct (Sint63.lebP a b); symmetry;
    [apply Z.leb_le | apply Z.leb_gt]; lia.
Qed.

Lemma eqb_m : forall a b : int, (a =? b)%uint63 = (sZ a =? sZ b).
Proof.
  intros a b. destruct (a =? b)%uint63 eqn:E.
  - apply eqb_spec in E. subst. symmetry. apply Z.eqb_refl.
  - symmetry. apply Z.eqb_neq. intros H. apply Sint63.to_Z_inj in H. subst.
    rewrite eqb_refl in E. discriminate.
Qed.

Lemma lexle_m_eq : forall a b c d,
  lexle_m a b c d = lexle (sZ a) (sZ b) (sZ c) (sZ d).
Proof. intros. unfold lexle_m, lexle. rewrite ltb_m, eqb_m, leb_m. reflexivity. Qed.

Lemma lexlt_m_eq : forall a b c d,
  lexlt_m a b c d = lexlt (sZ a) (sZ b) (sZ c) (sZ d).
Proof. intros. unfold lexlt_m, lexlt. rewrite !ltb_m, eqb_m. reflexivity. Qed.

Lemma repr_Empty : repr (Empty : inter sint) (Empty : inter Z).
Proof. exact I. Qed.

Lemma repr_Point : forall a b c A B C, sZ a = A -> sZ b = B -> sZ c = C ->
  repr (Point a b c : inter sint) (Point A B C : inter Z).
Proof. intros. repeat split; assumption. Qed.

Lemma repr_Segment : forall a b c e A B C E, sZ a = A -> sZ b = B -> sZ c = C -> sZ e = E ->
  repr (Segment a b c e : inter sint) (Segment A B C E : inter Z).
Proof. intros. repeat split; assumption. Qed.

Lemma finish_m_repr : forall a b c d,
  repr (finish_m a b c d) (finishZ (sZ a) (sZ b) (sZ c) (sZ d)).
Proof.
  intros. unfold finish_m, finishZ. rewrite lexlt_m_eq, !eqb_m.
  destruct (lexlt _ _ _ _); [apply repr_Segment; reflexivity|].
  destruct (_ && _); [apply repr_Point; reflexivity|apply repr_Empty].
Qed.

Lemma coll2_m_repr : forall a b c d e f g h,
  repr (coll2_m a b c d e f g h)
       (coll2Z (sZ a) (sZ b) (sZ c) (sZ d) (sZ e) (sZ f) (sZ g) (sZ h)).
Proof.
  intros. unfold coll2_m, coll2Z. rewrite !lexle_m_eq.
  destruct (lexle _ _ _ _); destruct (lexle _ _ _ _); apply finish_m_repr.
Qed.

Lemma coll_m_repr : forall a b c d e f g h,
  repr (coll_m a b c d e f g h)
       (collZ (sZ a) (sZ b) (sZ c) (sZ d) (sZ e) (sZ f) (sZ g) (sZ h)).
Proof.
  intros. unfold coll_m, collZ, coll1_m, coll1Z. rewrite !lexle_m_eq.
  destruct (lexle _ _ _ _); destruct (lexle _ _ _ _); apply coll2_m_repr.
Qed.

(* exact arithmetic under the bounds *)

Lemma min_max_int : sZ Sint63.min_int = -4611686018427387904 /\
                    sZ Sint63.max_int = 4611686018427387903.
Proof. split; reflexivity. Qed.

Lemma pow61 : 2 ^ 61 = 2305843009213693952.
Proof. reflexivity. Qed.

Lemma pow60 : 2 ^ 60 = 1152921504606846976.
Proof. reflexivity. Qed.

Lemma val_sub : forall a b : int, Z.abs (sZ a) <= 2 ^ 60 -> Z.abs (sZ b) <= 2 ^ 60 ->
  sZ (a - b)%uint63 = sZ a - sZ b.
Proof. intros. apply Sint63.to_Z_sub. rewrite ?pow60, ?pow61 in *.
  change (sZ Sint63.min_int) with (-4611686018427387904).
  change (sZ Sint63.max_int) with 4611686018427387903. lia. Qed.

Lemma val_add : forall a b : int, Z.abs (sZ a) <= 2 ^ 60 -> Z.abs (sZ b) <= 2 ^ 60 ->
  sZ (a + b)%uint63 = sZ a + sZ b.
Proof. intros. apply Sint63.to_Z_add. rewrite ?pow60, ?pow61 in *.
  change (sZ Sint63.min_int) with (-4611686018427387904).
  change (sZ Sint63.max_int) with 4611686018427387903. lia. Qed.

Lemma val_mul : forall a b : int, Z.abs (sZ a * sZ b) <= 2 ^ 61 ->
  sZ (a * b)%uint63 = sZ a * sZ b.
Proof. intros. apply Sint63.to_Z_mul. rewrite ?pow60, ?pow61 in *.
  change (sZ Sint63.min_int) with (-4611686018427387904).
  change (sZ Sint63.max_int) with 4611686018427387903. lia. Qed.

Lemma abs_mul_le : forall x y X Y, Z.abs x <= X -> Z.abs y <= Y -> Z.abs (x * y) <= X * Y.
Proof.
  intros. rewrite Z.abs_mul. apply Z.mul_le_mono_nonneg; lia.
Qed.

Definition small (z : Z) : Prop := Z.abs z <= 10000.

Lemma val_d : forall a b : int, small (sZ a) -> small (sZ b) ->
  sZ (a - b)%uint63 = sZ a - sZ b /\ Z.abs (sZ a - sZ b) <= 20000.
Proof. unfold small. intros. split; [apply val_sub; lia | lia]. Qed.

Lemma val_pd : forall a b c e : int, small (sZ a) -> small (sZ b) -> small (sZ c) -> small (sZ e) ->
  sZ ((a - b) * (c - e))%uint63 = (sZ a - sZ b) * (sZ c - sZ e) /\
  Z.abs ((sZ a - sZ b) * (sZ c - sZ e)) <= 400000000.
Proof.
  intros a b c e Ha Hb Hc He.
  destruct (val_d a b Ha Hb) as [E1 B1]. destruct (val_d c e Hc He) as [E2 B2].
  pose proof (abs_mul_le _ _ _ _ B1 B2) as B.
  split; [|lia].
  rewrite val_mul; rewrite E1, E2; [reflexivity | lia].
Qed.

Lemma val_cross : forall a b c e f g h i : int,
  small (sZ a) -> small (sZ b) -> small (sZ c) -> small (sZ e) ->
  small (sZ f) -> small (sZ g) -> small (sZ h) -> small (sZ i) ->
  sZ ((a - b) * (c - e) - (f - g) * (h - i))%uint63
    = (sZ a - sZ b) * (sZ c - sZ e) - (sZ f - sZ g) * (sZ h - sZ i) /\
  Z.abs ((sZ a - sZ b) * (sZ c - sZ e) - (sZ f - sZ g) * (sZ h - sZ i)) <= 800000000.
Proof.
  intros.
  destruct (val_pd a b c e) as [E1 B1]; try assumption.
  destruct (val_pd f g h i) as [E2 B2]; try assumption.
  split; [|lia].
  rewrite val_sub; rewrite ?E1, ?E2; [reflexivity | lia | lia].
Qed.

Lemma onseg_m_eq : forall a b c d e f,
  small (sZ a) -> small (sZ b) -> small (sZ c) -> small (sZ d) ->
  small (sZ e) -> small (sZ f) ->
  onseg_m a b c d e f = onsegbZ (sZ a) (sZ b) (sZ c) (sZ d) (sZ e) (sZ f).
Proof.
  intros. unfold onseg_m, onsegbZ. rewrite eqb_m, !leb_m.
  rewrite (proj1 (val_pd c a f b ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption))).
  rewrite (proj1 (val_pd d b e a ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption))).
  reflexivity.
Qed.

Lemma cross_fin_m_repr : forall (x1 y1 rx ry den tn un : int) X1 Y1 RX RY DEN TN UN,
  sZ x1 = X1 -> sZ y1 = Y1 -> sZ rx = RX -> sZ ry = RY ->
  sZ den = DEN -> sZ tn = TN -> sZ un = UN ->
  small X1 -> small Y1 -> Z.abs RX <= 20000 -> Z.abs RY <= 20000 ->
  Z.abs DEN <= 800000000 -> Z.abs TN <= 800000000 ->
  repr (cross_fin_m x1 y1 rx ry den tn un) (cross_finZ X1 Y1 RX RY DEN TN UN).
Proof.
  unfold small.
  intros x1 y1 rx ry den tn un X1 Y1 RX RY DEN TN UN Ex1 Ey1 Erx Ery Eden Etn Eun
    Bx1 By1 Brx Bry Bden Btn.
  unfold cross_fin_m, cross_finZ. rewrite !leb_m.
  change (sZ 0) with 0. rewrite Etn, Eden, Eun.
  destruct (_ && _); [|apply repr_Empty].
  pose proof (abs_mul_le _ _ _ _ Bx1 Bden). pose proof (abs_mul_le _ _ _ _ Btn Brx).
  pose proof (abs_mul_le _ _ _ _ By1 Bden). pose proof (abs_mul_le _ _ _ _ Btn Bry).
  apply repr_Point; [| |exact Eden].
  - rewrite val_add; rewrite ?val_mul; subst; lia.
  - rewrite val_add; rewrite ?val_mul; subst; lia.
Qed.

Lemma val_neg : forall a : int, Z.abs (sZ a) <= 2 ^ 60 -> sZ (0 - a)%uint63 = - sZ a.
Proof. intros. rewrite val_sub; [reflexivity | | assumption]. change (sZ 0) with 0. lia. Qed.

Lemma crossing_m_repr : forall (x1 y1 rx ry den tn un : int) X1 Y1 RX RY DEN TN UN,
  sZ x1 = X1 -> sZ y1 = Y1 -> sZ rx = RX -> sZ ry = RY ->
  sZ den = DEN -> sZ tn = TN -> sZ un = UN ->
  small X1 -> small Y1 -> Z.abs RX <= 20000 -> Z.abs RY <= 20000 ->
  Z.abs DEN <= 800000000 -> Z.abs TN <= 800000000 -> Z.abs UN <= 800000000 ->
  repr (crossing_m x1 y1 rx ry den tn un) (crossingZ X1 Y1 RX RY DEN TN UN).
Proof.
  intros x1 y1 rx ry den tn un X1 Y1 RX RY DEN TN UN Ex1 Ey1 Erx Ery Eden Etn Eun
    Bx1 By1 Brx Bry Bden Btn Bun.
  unfold crossing_m, crossingZ. rewrite ltb_m. change (sZ 0) with 0. rewrite Eden.
  destruct (DEN <? 0).
  - apply cross_fin_m_repr; try assumption; rewrite ?val_neg; subst; lia.
  - apply cross_fin_m_repr; assumption.
Qed.

Lemma isect_m_repr : forall a1 b1 a2 b2 a3 b3 a4 b4 : int,
  small (sZ a1) -> small (sZ b1) -> small (sZ a2) -> small (sZ b2) ->
  small (sZ a3) -> small (sZ b3) -> small (sZ a4) -> small (sZ b4) ->
  repr (isect_m a1 b1 a2 b2 a3 b3 a4 b4)
       (isectZ (sZ a1) (sZ b1) (sZ a2) (sZ b2) (sZ a3) (sZ b3) (sZ a4) (sZ b4)).
Proof.
  intros a1 b1 a2 b2 a3 b3 a4 b4 H1 H2 H3 H4 H5 H6 H7 H8.
  unfold isect_m, isectZ. cbv zeta.
  destruct (val_cross a2 a1 b4 b3 b2 b1 a4 a3) as [Eden Bden]; try assumption.
  destruct (val_cross a3 a1 b4 b3 b3 b1 a4 a3) as [Etn Btn]; try assumption.
  destruct (val_cross a3 a1 b2 b1 b3 b1 a2 a1) as [Eun Bun]; try assumption.
  destruct (val_d a2 a1) as [Erx Brx]; try assumption.
  destruct (val_d b2 b1) as [Ery Bry]; try assumption.
  destruct (val_d a4 a3) as [Esx Bsx]; try assumption.
  destruct (val_d b4 b3) as [Esy Bsy]; try assumption.
  rewrite !eqb_m. change (sZ 0) with 0.
  rewrite Eden, Eun, Erx, Ery, Esx, Esy.
  rewrite !onseg_m_eq by assumption.
  destruct (_ =? 0).
  - destruct ((sZ a2 - sZ a1 =? 0) && (sZ b2 - sZ b1 =? 0)).
    { destruct (onsegbZ _ _ _ _ _ _); [apply repr_Point; reflexivity | apply repr_Empty]. }
    destruct ((sZ a4 - sZ a3 =? 0) && (sZ b4 - sZ b3 =? 0)).
    { destruct (onsegbZ _ _ _ _ _ _); [apply repr_Point; reflexivity | apply repr_Empty]. }
    destruct (_ =? 0); [apply coll_m_repr | apply repr_Empty].
  - apply crossing_m_repr; first [reflexivity | assumption].
Qed.

(* ------------------------------------------------------------------ *)
(* The contract                                                         *)
(* ------------------------------------------------------------------ *)

Theorem intersect_m_correct :
  forall (x1 y1 x2 y2 x3 y3 x4 y4 : Z)
         (a1 b1 a2 b2 a3 b3 a4 b4 : sint),
  valid_input x1 y1 x2 y2 x3 y3 x4 y4 ->
  repr a1 x1 -> repr b1 y1 -> repr a2 x2 -> repr b2 y2 ->
  repr a3 x3 -> repr b3 y3 -> repr a4 x4 -> repr b4 y4 ->
  exists r : inter Z,
    repr (isect_m a1 b1 a2 b2 a3 b3 a4 b4) r /\
    intersect_spec x1 y1 x2 y2 x3 y3 x4 y4 r.
Proof.
  intros x1 y1 x2 y2 x3 y3 x4 y4 a1 b1 a2 b2 a3 b3 a4 b4 [Hv] R1 R2 R3 R4 R5 R6 R7 R8.
  cbv [repr repr_sint] in R1, R2, R3, R4, R5, R6, R7, R8.
  subst.
  rewrite !List.Forall_cons_iff in Hv. unfold small.
  exists (isectZ (sZ a1) (sZ b1) (sZ a2) (sZ b2) (sZ a3) (sZ b3) (sZ a4) (sZ b4)).
  split; [apply isect_m_repr; unfold small; tauto | apply isectZ_ok].
Qed.

Definition intersect : sint -> sint -> sint -> sint -> sint -> sint -> sint -> sint
                       -> inter sint := isect_m.

Definition intersect_correct :
  forall (x1 y1 x2 y2 x3 y3 x4 y4 : Z)
         (a1 b1 a2 b2 a3 b3 a4 b4 : sint),
  valid_input x1 y1 x2 y2 x3 y3 x4 y4 ->
  repr a1 x1 -> repr b1 y1 -> repr a2 x2 -> repr b2 y2 ->
  repr a3 x3 -> repr b3 y3 -> repr a4 x4 -> repr b4 y4 ->
  exists r : inter Z,
    repr (intersect a1 b1 a2 b2 a3 b3 a4 b4) r /\
    intersect_spec x1 y1 x2 y2 x3 y3 x4 y4 r
  := intersect_m_correct.
