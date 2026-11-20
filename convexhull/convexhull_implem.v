(* Implementation of convexhull (convexhull.spec): Andrew's monotone
   chain.  See README.md, section Implementation. *)

From Convexhull.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Sint63.
From KattisLib Require Import Cost.
Import ListNotations.

Open Scope bool_scope.
Open Scope uint63_scope.
Open Scope array_scope.

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
Elpi complexity sumbool.
Elpi complexity bdec.
Elpi complexity andb.

Definition gap (m j : int) : Z := ((φ m) - (φ j))%Z.

Lemma dec_step : forall m i : int,
  (i <? m) = true -> Zwf 0 (gap m (i + 1)) (gap m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

Lemma down_dec : forall j : int, (0 <? j) = true -> Zwf 0 (φ (j - 1)) (φ j).
Proof.
  intros j H. rewrite ltb_spec in H. change (φ 0) with 0%Z in H.
  unfold Zwf. sia.
Qed.

Lemma pop_dec : forall (lim k : int) (b : bool),
  ((lim <? k) && b) = true -> Zwf 0 (φ (k - 1)) (φ k).
Proof.
  intros lim k b H. apply andb_prop in H. destruct H as [H _].
  rewrite ltb_spec in H. pose proof (to_Z_bounded lim).
  unfold Zwf. sia.
Qed.

Definition min_i (a b : int) : int := if a <? b then a else b.
Elpi complexity min_i.
Arguments min_i_cost : simpl never.

Lemma pass_dec : forall n lo w : int,
  (lo <? min_i (lo + w + w) n) = true ->
  Zwf 0 (gap n (min_i (lo + w + w) n)) (gap n lo).
Proof.
  intros n lo w H. unfold Zwf, gap, min_i in *.
  destruct (lo + w + w <? n) eqn:E; rewrite ltb_spec in *; lia.
Qed.

Definition mz (n w : int) : Z := Z.max 0 ((φ n) - (φ w)).

Lemma sort_dec : forall n w : int,
  ((w <? n) && (w <? w + w)) = true -> Zwf 0 (mz n (w + w)) (mz n w).
Proof.
  intros n w H. apply andb_prop in H. destruct H as [H1 H2].
  rewrite ltb_spec in H1, H2. unfold Zwf, mz. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* Twice the signed area of the triangle of the points of indices a b c. *)
Definition cross_m (x y : array int) (a b c : int) : int :=
  let xa := x.[a] in
  let ya := y.[a] in
  (x.[b] - xa) * (y.[c] - ya) - (y.[b] - ya) * (x.[c] - xa).
Elpi complexity cross_m.
Arguments cross_m_cost : simpl never.

(* Lexicographic (x, y) comparison of the points of indices a and b. *)
Definition le_pt (x y : array int) (a b : int) : bool :=
  let xa := x.[a] in
  let xb := x.[b] in
  if Sint63.ltb xa xb then true
  else if xa =? xb then Sint63.leb y.[a] y.[b] else false.
Elpi complexity le_pt.
Arguments le_pt_cost : simpl never.

Definition take_left (x y src : array int) (mid hi i j : int) : bool :=
  if i <? mid then (if j <? hi then le_pt x y src.[i] src.[j] else true)
  else false.
Elpi complexity take_left.
Arguments take_left_cost : simpl never.

(* Merge the sorted runs src[i, mid) and src[j, hi) into dst[k, hi). *)
Fixpoint merge (x y src : array int) (mid hi i j k : int) (dst : array int)
    (H : Acc (Zwf 0) (gap hi k)) {struct H} : array int :=
  match bdec (k <? hi) with
  | left Hk =>
      if take_left x y src mid hi i j
      then merge x y src mid hi (i + 1) j (k + 1) dst.[k <- src.[i]]
             (Acc_inv H (dec_step hi k Hk))
      else merge x y src mid hi i (j + 1) (k + 1) dst.[k <- src.[j]]
             (Acc_inv H (dec_step hi k Hk))
  | right _ => dst
  end.
Elpi complexity merge.
Arguments merge_cost : simpl never.

(* One pass of the bottom-up merge sort: runs of width w into runs of
   width 2w, from src into dst, blocks lo, lo + 2w, ... *)
Fixpoint pass (x y src : array int) (w n lo : int) (dst : array int)
    (H : Acc (Zwf 0) (gap n lo)) {struct H} : array int :=
  match bdec (lo <? min_i (lo + w + w) n) with
  | left Hl =>
      pass x y src w n (min_i (lo + w + w) n)
        (merge x y src (min_i (lo + w) n) (min_i (lo + w + w) n)
           lo (min_i (lo + w) n) lo dst
           (Zwf_well_founded 0 (gap (min_i (lo + w + w) n) lo)))
        (Acc_inv H (pass_dec n lo w Hl))
  | right _ => dst
  end.
Elpi complexity pass.
Arguments pass_cost : simpl never.

Fixpoint sortl (x y : array int) (n w : int) (src dst : array int)
    (H : Acc (Zwf 0) (mz n w)) {struct H} : array int :=
  match bdec ((w <? n) && (w <? w + w)) with
  | left Hw =>
      sortl x y n (w + w)
        (pass x y src w n 0 dst (Zwf_well_founded 0 (gap n 0))) src
        (Acc_inv H (sort_dec n w Hw))
  | right _ => src
  end.
Elpi complexity sortl.
Arguments sortl_cost : simpl never.

Fixpoint initl (n i : int) (a : array int) (H : Acc (Zwf 0) (gap n i))
    {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi => initl n (i + 1) a.[i <- i] (Acc_inv H (dec_step n i Hi))
  | right _ => a
  end.
Elpi complexity initl.
Arguments initl_cost : simpl never.

(* The indices 0 .. n-1 sorted by (x, y). *)
Definition msort (x y : array int) (n : int) : array int :=
  sortl x y n 1
    (initl n 0 (PArray.make n 0) (Zwf_well_founded 0 (gap n 0)))
    (PArray.make n 0) (Zwf_well_founded 0 (mz n 1)).
Elpi complexity msort.
Arguments msort_cost : simpl never.

(* Pop the stack st[0, k) while it has more than lim cells and its two
   top points do not turn strictly left towards q. *)
Fixpoint pop (x y st : array int) (lim k q : int) (H : Acc (Zwf 0) (φ k))
    {struct H} : int :=
  match bdec ((lim <? k) && Sint63.leb (cross_m x y st.[k - 2] st.[k - 1] q) 0)
  with
  | left Hc => pop x y st lim (k - 1) q (Acc_inv H (pop_dec lim k _ Hc))
  | right _ => k
  end.
Elpi complexity pop.
Arguments pop_cost : simpl never.

(* The lower chain: sorted positions i .. n-1. *)
Fixpoint lower (x y ord st : array int) (n k i : int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int * int :=
  match bdec (i <? n) with
  | left Hi =>
      let q := ord.[i] in
      let k' := pop x y st 1 k q (Zwf_well_founded 0 (φ k)) in
      lower x y ord st.[k' <- q] n (k' + 1) (i + 1) (Acc_inv H (dec_step n i Hi))
  | right _ => (st, k)
  end.
Elpi complexity lower.
Arguments lower_cost : simpl never.

(* The upper chain: sorted positions j-1 down to 0, above the lim cells
   of the lower chain. *)
Fixpoint upper (x y ord st : array int) (lim k j : int)
    (H : Acc (Zwf 0) (φ j)) {struct H} : array int * int :=
  match bdec (0 <? j) with
  | left Hj =>
      let q := ord.[j - 1] in
      let k' := pop x y st lim k q (Zwf_well_founded 0 (φ k)) in
      upper x y ord st.[k' <- q] lim (k' + 1) (j - 1) (Acc_inv H (down_dec j Hj))
  | right _ => (st, k)
  end.
Elpi complexity upper.
Arguments upper_cost : simpl never.

Fixpoint copyl (src dst : array int) (h i : int) (H : Acc (Zwf 0) (gap h i))
    {struct H} : array int :=
  match bdec (i <? h) with
  | left Hi => copyl src dst.[i <- src.[i]] h (i + 1) (Acc_inv H (dec_step h i Hi))
  | right _ => dst
  end.
Elpi complexity copyl.
Arguments copyl_cost : simpl never.

Definition hull (x y : array sint) : array uint :=
  let n := PArray.length x in
  let ord := msort x y n in
  let a := ord.[0] in
  let b := ord.[n - 1] in
  if (x.[a] =? x.[b]) && (y.[a] =? y.[b]) then PArray.make 1 a
  else
    let '(st1, l) := lower x y ord (PArray.make (n + n) 0).[0 <- a] n 1 1
                       (Zwf_well_founded 0 (gap n 1)) in
    let '(st2, k) := upper x y ord st1 l l (n - 1)
                       (Zwf_well_founded 0 (φ (n - 1))) in
    copyl st2 (PArray.make (k - 1) 0) (k - 1) 0
      (Zwf_well_founded 0 (gap (k - 1) 0)).
Elpi complexity hull.
Arguments hull_cost : simpl never.

(* ------------------------------------------------------------------ *)
(* Geometry on Z points                                                *)
(* ------------------------------------------------------------------ *)

Section Geometry.
Local Open Scope Z_scope.

(* Lexicographic order on points. *)
Definition lex (a b : point) : Prop :=
  fst a < fst b \/ (fst a = fst b /\ snd a <= snd b).

Definition negp (a : point) : point := (- fst a, - snd a).

Lemma lex_refl : forall a, lex a a.
Proof. intros [a1 a2]; unfold lex; simpl; lia. Qed.

Lemma lex_trans : forall a b c, lex a b -> lex b c -> lex a c.
Proof. intros [a1 a2] [b1 b2] [c1 c2]; unfold lex; simpl; lia. Qed.

Lemma lex_total : forall a b, lex a b \/ lex b a.
Proof. intros [a1 a2] [b1 b2]; unfold lex; simpl; lia. Qed.

Lemma lex_antisym : forall a b, lex a b -> lex b a -> a = b.
Proof.
  intros [a1 a2] [b1 b2]; unfold lex; simpl; intros H1 H2.
  f_equal; lia.
Qed.

Lemma lex_neg : forall a b, lex (negp a) (negp b) <-> lex b a.
Proof. intros [a1 a2] [b1 b2]; unfold lex, negp; simpl; lia. Qed.

Lemma negp_inj : forall a b, negp a = negp b -> a = b.
Proof.
  intros [a1 a2] [b1 b2]; unfold negp; simpl; intros H.
  injection H; intros; f_equal; lia.
Qed.

Lemma cross_neg : forall a b c, cross (negp a) (negp b) (negp c) = cross a b c.
Proof. intros [a1 a2] [b1 b2] [c1 c2]; unfold cross, negp; simpl; ring. Qed.

Lemma cross_cyc : forall a b c, cross a b c = cross b c a.
Proof. intros [a1 a2] [b1 b2] [c1 c2]; unfold cross; simpl; ring. Qed.

Lemma cross_swap : forall a b c, cross b a c = - cross a b c.
Proof. intros [a1 a2] [b1 b2] [c1 c2]; unfold cross; simpl; ring. Qed.

Lemma cross_aac : forall a c, cross a a c = 0.
Proof. intros [a1 a2] [c1 c2]; unfold cross; simpl; ring. Qed.

Lemma cross_abb : forall a b, cross a b b = 0.
Proof. intros [a1 a2] [b1 b2]; unfold cross; simpl; ring. Qed.

Lemma cross_aba : forall a b, cross a b a = 0.
Proof. intros [a1 a2] [b1 b2]; unfold cross; simpl; ring. Qed.

(* popping: p was left of (a, b) and of (b, q). *)
Lemma geo_pop1 : forall a b p q,
  0 <= cross a b p -> 0 <= cross b q p -> cross a b q <= 0 -> 0 <= cross a q p.
Proof.
  intros [a1 a2] [b1 b2] [p1 p2] [q1 q2]; unfold cross; simpl; intros; nia.
Qed.

(* popping: p between a and b. *)
Lemma geo_pop2 : forall a b p q,
  lex a p -> lex p b -> lex a q ->
  0 <= cross a b p -> cross a b q <= 0 -> 0 <= cross a q p.
Proof.
  intros [a1 a2] [b1 b2] [p1 p2] [q1 q2]; unfold lex; simpl; intros H1 H2 H3 H4 H5.
  assert (Id : cross (a1, a2) (q1, q2) (p1, p2) * (b1 - a1) =
     cross (a1, a2) (b1, b2) (p1, p2) * (q1 - a1)
     - cross (a1, a2) (b1, b2) (q1, q2) * (p1 - a1))
    by (unfold cross; simpl; ring).
  destruct (Z.lt_ge_cases a1 b1) as [Hab | Hab].
  - assert (0 <= cross (a1, a2) (b1, b2) (p1, p2) * (q1 - a1)) by (apply Z.mul_nonneg_nonneg; lia).
    assert (0 <= - cross (a1, a2) (b1, b2) (q1, q2) * (p1 - a1)) by (apply Z.mul_nonneg_nonneg; lia).
    nia.
  - assert (p1 = a1) by lia. assert (b1 = a1) by lia. subst.
    unfold cross in *; simpl in *. nia.
Qed.

(* pushing q: a point p before a, left of (b, a), is left of (a, q). *)
Lemma geo_push : forall b a p q,
  lex b a -> lex p a -> lex a q ->
  0 <= cross b a p -> 0 < cross b a q -> 0 <= cross a q p.
Proof.
  intros [b1 b2] [a1 a2] [p1 p2] [q1 q2]; unfold lex; simpl; intros H1 H2 H3 H4 H5.
  assert (Id : cross (a1, a2) (q1, q2) (p1, p2) * (b1 - a1) =
     cross (b1, b2) (a1, a2) (q1, q2) * (p1 - a1)
     - cross (b1, b2) (a1, a2) (p1, p2) * (q1 - a1))
    by (unfold cross; simpl; ring).
  destruct (Z.lt_ge_cases b1 a1) as [Hab | Hab].
  - assert (0 <= cross (b1, b2) (a1, a2) (q1, q2) * (a1 - p1)) by (apply Z.mul_nonneg_nonneg; lia).
    assert (0 <= cross (b1, b2) (a1, a2) (p1, p2) * (q1 - a1)) by (apply Z.mul_nonneg_nonneg; lia).
    nia.
  - assert (b1 = a1) by lia. subst.
    unfold cross in *; simpl in *. nia.
Qed.

(* convexity propagates "q left of the edge" backwards along a chain. *)
Lemma geo_back : forall a b c q,
  lex a b -> lex b c -> lex c q ->
  0 < cross a b c -> 0 <= cross b c q -> 0 <= cross a b q.
Proof.
  intros [a1 a2] [b1 b2] [c1 c2] [q1 q2]; unfold lex; simpl; intros H1 H2 H3 H4 H5.
  assert (Id : cross (a1, a2) (b1, b2) (q1, q2) * (c1 - b1) =
     cross (a1, a2) (b1, b2) (c1, c2) * (q1 - b1)
     - cross (b1, b2) (c1, c2) (q1, q2) * (a1 - b1))
    by (unfold cross; simpl; ring).
  destruct (Z.lt_ge_cases b1 c1) as [Hbc | Hbc].
  - assert (0 <= cross (a1, a2) (b1, b2) (c1, c2) * (q1 - b1)) by (apply Z.mul_nonneg_nonneg; lia).
    assert (0 <= cross (b1, b2) (c1, c2) (q1, q2) * (b1 - a1)) by (apply Z.mul_nonneg_nonneg; lia).
    nia.
  - assert (c1 = b1) by lia. subst.
    unfold cross in *; simpl in *. nia.
Qed.

(* two collinear edges meeting at m from the same side: everything on the
   line. *)
Lemma geo_coll : forall s m u p,
  lex s m -> s <> m -> lex u m -> u <> m -> cross s m u = 0 ->
  0 <= cross s m p -> 0 <= cross m u p -> cross s m p = 0.
Proof.
  intros [s1 s2] [m1 m2] [u1 u2] [p1 p2]; unfold lex; simpl;
    intros H1 H2 H3 H4 H5 H6 H7.
  assert (Ix : cross (s1, s2) (m1, m2) (p1, p2) * (u1 - m1)
             + cross (m1, m2) (u1, u2) (p1, p2) * (s1 - m1)
             = cross (s1, s2) (m1, m2) (u1, u2) * (p1 - m1))
    by (unfold cross; simpl; ring).
  assert (Iy : cross (s1, s2) (m1, m2) (p1, p2) * (u2 - m2)
             + cross (m1, m2) (u1, u2) (p1, p2) * (s2 - m2)
             = cross (s1, s2) (m1, m2) (u1, u2) * (p2 - m2))
    by (unfold cross; simpl; ring).
  rewrite H5 in Ix, Iy.
  set (X := cross (s1, s2) (m1, m2) (p1, p2)) in *.
  set (T := cross (m1, m2) (u1, u2) (p1, p2)) in *.
  destruct (Z.eq_dec X 0) as [E | E]; [exact E | exfalso].
  assert (HX : 0 < X) by lia.
  assert (A1 : X * (u1 - m1) <= 0) by (apply Z.mul_nonneg_nonpos; lia).
  assert (A2 : T * (s1 - m1) <= 0) by (apply Z.mul_nonneg_nonpos; lia).
  assert (A3 : X * (u1 - m1) = 0) by lia.
  assert (U1 : u1 = m1) by nia.
  assert (U2 : u2 < m2).
  { destruct H3 as [H3 | [_ H3]]; [lia|]. destruct (Z.eq_dec u2 m2); [|lia].
    subst; contradiction. }
  assert (A4 : X * (u2 - m2) < 0) by nia.
  assert (A5 : T * (s1 - m1) = 0) by lia.
  destruct (Z.eq_dec T 0) as [ET | ET]; [rewrite ET in Iy; lia|].
  assert (S1 : s1 = m1) by nia.
  assert (S2 : s2 < m2).
  { destruct H1 as [H1 | [_ H1]]; [lia|]. destruct (Z.eq_dec s2 m2); [|lia].
    subst; contradiction. }
  nia.
Qed.

(* all points on the line through s and m are collinear. *)
Lemma geo_col3 : forall s m p r,
  s <> m -> cross s m p = 0 -> cross s m r = 0 -> cross m p r = 0.
Proof.
  intros [s1 s2] [m1 m2] [p1 p2] [r1 r2] H1 H2 H3.
  assert (Ix : cross (m1, m2) (p1, p2) (r1, r2) * (s1 - m1)
             = - cross (s1, s2) (m1, m2) (r1, r2) * (p1 - m1)
               + cross (s1, s2) (m1, m2) (p1, p2) * (r1 - m1))
    by (unfold cross; simpl; ring).
  assert (Iy : cross (m1, m2) (p1, p2) (r1, r2) * (s2 - m2)
             = - cross (s1, s2) (m1, m2) (r1, r2) * (p2 - m2)
               + cross (s1, s2) (m1, m2) (p1, p2) * (r2 - m2))
    by (unfold cross; simpl; ring).
  rewrite H2, H3 in Ix, Iy.
  destruct (Z.eq_dec s1 m1) as [E1 | E1].
  - destruct (Z.eq_dec s2 m2) as [E2 | E2]; [subst; contradiction|].
    nia.
  - nia.
Qed.

(* a vertex v cannot be visited by both chains. *)
Lemma geo_nodup : forall v c a' a,
  lex v c -> v <> c -> lex a' v -> a' <> v ->
  0 <= cross v a' c -> 0 <= cross v c a' -> 0 <= cross v a' a ->
  0 < cross a v c -> False.
Proof.
  intros [v1 v2] [c1 c2] [b1 b2] [a1 a2]; unfold lex; simpl;
    intros H1 H2 H3 H4 H5 H6 H7 H8.
  assert (Z0 : cross (v1, v2) (b1, b2) (c1, c2) = 0).
  { assert (cross (v1, v2) (c1, c2) (b1, b2) = - cross (v1, v2) (b1, b2) (c1, c2))
      by (unfold cross; simpl; ring). lia. }
  assert (Ix : cross (a1, a2) (v1, v2) (c1, c2) * (b1 - v1)
             = cross (v1, v2) (b1, b2) (a1, a2) * (c1 - v1)
               - cross (v1, v2) (b1, b2) (c1, c2) * (a1 - v1))
    by (unfold cross; simpl; ring).
  assert (Iy : cross (a1, a2) (v1, v2) (c1, c2) * (b2 - v2)
             = cross (v1, v2) (b1, b2) (a1, a2) * (c2 - v2)
               - cross (v1, v2) (b1, b2) (c1, c2) * (a2 - v2))
    by (unfold cross; simpl; ring).
  rewrite Z0 in Ix, Iy.
  set (K := cross (a1, a2) (v1, v2) (c1, c2)) in *.
  set (M := cross (v1, v2) (b1, b2) (a1, a2)) in *.
  assert (A1 : K * (b1 - v1) <= 0) by (apply Z.mul_nonneg_nonpos; lia).
  assert (A2 : 0 <= M * (c1 - v1)) by (apply Z.mul_nonneg_nonneg; lia).
  assert (B1 : b1 = v1) by nia.
  assert (B2 : b2 < v2).
  { destruct H3 as [H3 | [_ H3]]; [lia|]. destruct (Z.eq_dec b2 v2); [|lia].
    subst; contradiction. }
  assert (A3 : K * (b2 - v2) < 0) by nia.
  destruct (Z.eq_dec c1 v1) as [C1 | C1].
  - assert (C2 : v2 < c2).
    { destruct H1 as [H1 | [_ H1]]; [lia|]. destruct (Z.eq_dec c2 v2); [|lia].
      subst; contradiction. }
    nia.
  - assert (M * (c1 - v1) = 0) by lia.
    assert (EM : M = 0) by nia. rewrite EM in Iy. lia.
Qed.

(* the two-vertex case. *)
Lemma geo_seg : forall a b p,
  lex a p -> lex p b -> cross a b p = 0 -> on_segment a b p.
Proof.
  intros [a1 a2] [b1 b2] [p1 p2]; unfold lex, on_segment; simpl; intros H1 H2 H3.
  split; [exact H3|].
  unfold cross in H3; simpl in H3.
  split; [lia|].
  destruct (Z.eq_dec a1 b1) as [E | E].
  - assert (p1 = a1) by lia. lia.
  - assert (a1 < b1) by lia.
    destruct (Z.le_ge_cases a2 b2).
    + assert (a2 <= p2) by nia. assert (p2 <= b2) by nia. lia.
    + assert (p2 <= a2) by nia. assert (b2 <= p2) by nia. lia.
Qed.

End Geometry.

(* ------------------------------------------------------------------ *)
(* The chain invariant, abstractly                                     *)
(* ------------------------------------------------------------------ *)

Section Chain.
Local Open Scope Z_scope.

(* c b .. c t is the stack (bottom b, top t); Pr is the set of the points
   processed so far. *)
Record chain (c : Z -> point) (b t : Z) (Pr : point -> Prop) : Prop := {
  ch_bt : b <= t;
  ch_le : forall j, b <= j < t -> lex (c j) (c (j + 1));
  ch_cvx : forall j, b <= j -> j + 2 <= t -> 0 < cross (c j) (c (j + 1)) (c (j + 2));
  ch_left : forall j p, b <= j < t -> Pr p -> 0 <= cross (c j) (c (j + 1)) p;
  ch_top : forall p, Pr p -> lex p (c t);
  ch_bot : forall p, Pr p -> lex (c b) p;
  ch_in : Pr (c t);
}.

Lemma mono_of_steps : forall (c : Z -> point) b t,
  (forall j, b <= j < t -> lex (c j) (c (j + 1))) ->
  forall i j, b <= i -> i <= j -> j <= t -> lex (c i) (c j).
Proof.
  intros c b t Hs.
  assert (G : forall d : nat, forall i, b <= i -> i + Z.of_nat d <= t ->
            lex (c i) (c (i + Z.of_nat d))).
  { induction d as [| d IH]; intros i Hi Hd.
    - rewrite Z.add_0_r. apply lex_refl.
    - apply lex_trans with (c (i + Z.of_nat d)); [apply IH; lia|].
      replace (i + Z.of_nat (S d)) with (i + Z.of_nat d + 1) by lia.
      apply Hs; lia. }
  intros i j Hi Hij Hj.
  replace j with (i + Z.of_nat (Z.to_nat (j - i))) by lia.
  apply G; lia.
Qed.

Lemma chain_mono : forall c b t Pr, chain c b t Pr ->
  forall i j, b <= i -> i <= j -> j <= t -> lex (c i) (c j).
Proof. intros c b t Pr H. apply mono_of_steps. apply (ch_le _ _ _ _ H). Qed.

Definition popinv (c : Z -> point) (b t0 t : Z) (Pr : point -> Prop) (q : point) : Prop :=
  chain c b t0 Pr /\ b <= t <= t0 /\ lex (c t0) q /\
  (forall p, Pr p -> lex (c t) p -> 0 <= cross (c t) q p).

Lemma popinv_init : forall c b t0 Pr q,
  chain c b t0 Pr -> (forall p, Pr p -> lex p q) -> popinv c b t0 t0 Pr q.
Proof.
  intros c b t0 Pr q Hc Hq. pose proof (ch_bt _ _ _ _ Hc).
  split; [exact Hc|]. split; [lia|]. split; [apply Hq, (ch_in _ _ _ _ Hc)|].
  intros p Hp Hl.
  assert (p = c t0) by (apply lex_antisym; [apply (ch_top _ _ _ _ Hc); exact Hp | exact Hl]).
  subst p. rewrite cross_aba. lia.
Qed.

Lemma popinv_step : forall c b t0 t Pr q,
  popinv c b t0 t Pr q -> b < t -> cross (c (t - 1)) (c t) q <= 0 ->
  popinv c b t0 (t - 1) Pr q.
Proof.
  intros c b t0 t Pr q [Hc [Ht [Hq Hj]]] Hb Hx.
  split; [exact Hc|]. split; [lia|]. split; [exact Hq|].
  intros p Hp Hl.
  assert (Ht1 : t - 1 + 1 = t) by lia.
  assert (Hl1 : 0 <= cross (c (t - 1)) (c t) p)
    by (rewrite <- Ht1 at 2; apply (ch_left _ _ _ _ Hc); [lia | exact Hp]).
  destruct (lex_total (c t) p) as [Hcp | Hpc].
  - apply geo_pop1 with (c t); auto.
  - apply geo_pop2 with (c t); auto.
    apply lex_trans with (c t0); [|exact Hq].
    apply (chain_mono _ _ _ _ Hc); lia.
Qed.

Lemma chain_back : forall c b t0 t Pr q,
  popinv c b t0 t Pr q -> b < t -> 0 < cross (c (t - 1)) (c t) q ->
  forall j, b <= j < t -> 0 <= cross (c j) (c (j + 1)) q.
Proof.
  intros c b t0 t Pr q [Hc [Ht [Hq Hj]]] Hb Hx.
  assert (G : forall d : nat, forall j, j = t - 1 - Z.of_nat d -> b <= j ->
            0 <= cross (c j) (c (j + 1)) q).
  { induction d as [| d IH]; intros j Ej Hbj.
    - replace (j + 1) with t by lia. replace j with (t - 1) by lia. lia.
    - assert (IH1 := IH (j + 1) ltac:(lia) ltac:(lia)).
      replace (j + 1 + 1) with (j + 2) in IH1 by lia.
      apply geo_back with (c (j + 2)).
      + apply (ch_le _ _ _ _ Hc); lia.
      + replace (j + 2) with (j + 1 + 1) by lia. apply (ch_le _ _ _ _ Hc); lia.
      + apply lex_trans with (c t0); [|exact Hq]. apply (chain_mono _ _ _ _ Hc); lia.
      + apply (ch_cvx _ _ _ _ Hc); lia.
      + exact IH1. }
  intros j Hj'. apply (G (Z.to_nat (t - 1 - j))); lia.
Qed.

Lemma chain_push : forall c b t0 t Pr q,
  popinv c b t0 t Pr q ->
  (t = b \/ 0 < cross (c (t - 1)) (c t) q) ->
  (forall p, Pr p -> lex p q) ->
  forall (c' : Z -> point) (Pr' : point -> Prop),
  (forall j, b <= j <= t -> c' j = c j) -> c' (t + 1) = q ->
  (forall p, Pr' p -> Pr p \/ p = q) -> Pr' q ->
  chain c' b (t + 1) Pr'.
Proof.
  intros c b t0 t Pr q Hpi Hstop Hq c' Pr' Hc'1 Hc'2 HPr' HPrq.
  pose proof Hpi as [Hc [Ht [Hq0 Hj]]].
  assert (Hctq : lex (c t) q)
    by (apply lex_trans with (c t0); [apply (chain_mono _ _ _ _ Hc); lia | exact Hq0]).
  constructor.
  - lia.
  - intros j Hj'. destruct (Z.eq_dec j t) as [E | E].
    + subst j. rewrite Hc'2, Hc'1 by lia. exact Hctq.
    + rewrite !Hc'1 by lia. apply (ch_le _ _ _ _ Hc); lia.
  - intros j Hj1 Hj2. destruct (Z.eq_dec (j + 2) (t + 1)) as [E | E].
    + replace (j + 2) with (t + 1) by lia. rewrite Hc'2.
      replace j with (t - 1) by lia. replace (t - 1 + 1) with t by lia.
      rewrite !Hc'1 by lia. destruct Hstop as [Hs | Hs]; [lia | exact Hs].
    + rewrite !Hc'1 by lia. apply (ch_cvx _ _ _ _ Hc); lia.
  - intros j p Hj' Hp. destruct (Z.eq_dec j t) as [E | E].
    + subst j. rewrite Hc'2, Hc'1 by lia.
      destruct (HPr' p Hp) as [Hp' | Hp']; [| subst p; rewrite cross_abb; lia].
      destruct (lex_total (c t) p) as [Hcp | Hpc]; [apply Hj; assumption|].
      destruct (Z.eq_dec t b) as [Hs | Htb].
      * subst t. assert (p = c b)
          by (apply lex_antisym; [exact Hpc | apply (ch_bot _ _ _ _ Hc); exact Hp']).
        subst p. rewrite cross_aba. lia.
      * destruct Hstop as [Hs | Hs]; [lia|].
        apply geo_push with (c (t - 1)); auto.
        -- replace t with (t - 1 + 1) at 2 by lia. apply (ch_le _ _ _ _ Hc); lia.
        -- replace t with (t - 1 + 1) at 2 by lia. apply (ch_left _ _ _ _ Hc); [lia | exact Hp'].
    + rewrite !Hc'1 by lia.
      destruct (HPr' p Hp) as [Hp' | Hp'].
      * apply (ch_left _ _ _ _ Hc); [lia | exact Hp'].
      * subst p. destruct Hstop as [Hs | Hs]; [lia|].
        apply (chain_back c b t0 t Pr q Hpi ltac:(lia) Hs). lia.
  - intros p Hp. rewrite Hc'2. destruct (HPr' p Hp) as [Hp' | Hp'];
      [apply Hq; exact Hp' | subst; apply lex_refl].
  - intros p Hp. rewrite Hc'1 by lia. destruct (HPr' p Hp) as [Hp' | Hp'];
      [apply (ch_bot _ _ _ _ Hc); exact Hp' | subst p].
    apply lex_trans with (c t); [apply (chain_mono _ _ _ _ Hc); lia | exact Hctq].
  - rewrite Hc'2. exact HPrq.
Qed.

End Chain.

(* ------------------------------------------------------------------ *)
(* The closed polygon of the two chains, abstractly                    *)
(* ------------------------------------------------------------------ *)

Section Polygon.
Local Open Scope Z_scope.

(* e 0 .. e (L-1) is the lower chain, e (L-1) .. e (k-1) the upper one,
   e (k-1) = e 0; S is the set of the input points. *)
Variable e : Z -> point.
Variables L k : Z.
Variable S SN : point -> Prop.
Hypothesis HL : 2 <= L.
Hypothesis HK : L + 1 <= k.
Hypothesis Hlow : chain e 0 (L - 1) S.
Hypothesis Hup : chain (fun j => negp (e j)) (L - 1) (k - 1) SN.
Hypothesis HSN : forall p, S p -> SN (negp p).
Hypothesis Hend : e (k - 1) = e 0.
Hypothesis HAB : e 0 <> e (L - 1).
Hypothesis HS : forall j, 0 <= j < k -> S (e j).

Lemma low_le : forall j, 0 <= j < L - 1 -> lex (e j) (e (j + 1)).
Proof. apply (ch_le _ _ _ _ Hlow). Qed.

Lemma low_cvx : forall j, 0 <= j -> j + 2 <= L - 1 ->
  0 < cross (e j) (e (j + 1)) (e (j + 2)).
Proof. apply (ch_cvx _ _ _ _ Hlow). Qed.

Lemma low_left : forall j p, 0 <= j < L - 1 -> S p -> 0 <= cross (e j) (e (j + 1)) p.
Proof. apply (ch_left _ _ _ _ Hlow). Qed.

Lemma up_le : forall j, L - 1 <= j < k - 1 -> lex (e (j + 1)) (e j).
Proof. intros j Hj. apply lex_neg. apply (ch_le _ _ _ _ Hup). exact Hj. Qed.

Lemma up_cvx : forall j, L - 1 <= j -> j + 2 <= k - 1 ->
  0 < cross (e j) (e (j + 1)) (e (j + 2)).
Proof.
  intros j H1 H2. rewrite <- cross_neg. apply (ch_cvx _ _ _ _ Hup); assumption.
Qed.

Lemma up_left : forall j p, L - 1 <= j < k - 1 -> S p -> 0 <= cross (e j) (e (j + 1)) p.
Proof.
  intros j p Hj Hp. rewrite <- cross_neg.
  apply (ch_left _ _ _ _ Hup); [exact Hj | apply HSN; exact Hp].
Qed.

Lemma all_left : forall j p, 0 <= j < k - 1 -> S p -> 0 <= cross (e j) (e (j + 1)) p.
Proof.
  intros j p Hj Hp. destruct (Z.lt_ge_cases j (L - 1)).
  - apply low_left; [lia | exact Hp].
  - apply up_left; [lia | exact Hp].
Qed.

Lemma low_step : forall j, 0 <= j < L - 1 -> e j <> e (j + 1).
Proof.
  intros j Hj E.
  destruct (Z.eq_dec L 2) as [L2 | L2].
  - apply HAB. replace (L - 1) with 1 by lia. replace j with 0 in E by lia. exact E.
  - destruct (Z.le_gt_cases (j + 2) (L - 1)).
    + pose proof (low_cvx j ltac:(lia) ltac:(lia)) as C. rewrite E, cross_aac in C. lia.
    + pose proof (low_cvx (j - 1) ltac:(lia) ltac:(lia)) as C.
      replace (j - 1 + 1) with j in C by lia. replace (j - 1 + 2) with (j + 1) in C by lia.
      rewrite E, cross_abb in C. lia.
Qed.

Lemma up_step : forall j, L - 1 <= j < k - 1 -> e j <> e (j + 1).
Proof.
  intros j Hj E.
  destruct (Z.eq_dec k (L + 1)) as [K2 | K2].
  - apply HAB. replace j with (L - 1) in E by lia.
    replace (L - 1 + 1) with (k - 1) in E by lia. rewrite Hend in E. symmetry; exact E.
  - destruct (Z.le_gt_cases (j + 2) (k - 1)).
    + pose proof (up_cvx j ltac:(lia) ltac:(lia)) as C. rewrite E, cross_aac in C. lia.
    + pose proof (up_cvx (j - 1) ltac:(lia) ltac:(lia)) as C.
      replace (j - 1 + 1) with j in C by lia. replace (j - 1 + 2) with (j + 1) in C by lia.
      rewrite E, cross_abb in C. lia.
Qed.

Lemma low_strict : forall i j, 0 <= i < j -> j <= L - 1 -> lex (e i) (e j) /\ e i <> e j.
Proof.
  intros i j Hi Hj.
  assert (M : lex (e (i + 1)) (e j)) by (apply (mono_of_steps e 0 (L - 1) low_le); lia).
  pose proof (low_le i ltac:(lia)) as H1. pose proof (low_step i ltac:(lia)) as H2.
  split; [apply lex_trans with (e (i + 1)); assumption|].
  intro E. rewrite E in H1. apply H2. rewrite E. apply lex_antisym; assumption.
Qed.

Lemma up_mono : forall i j, L - 1 <= i -> i <= j -> j <= k - 1 -> lex (e j) (e i).
Proof.
  intros i j H1 H2 H3. apply lex_neg.
  apply (chain_mono _ _ _ _ Hup); lia.
Qed.

Lemma up_strict : forall i j, L - 1 <= i < j -> j <= k - 1 -> lex (e j) (e i) /\ e i <> e j.
Proof.
  intros i j Hi Hj.
  assert (M : lex (e j) (e (i + 1))) by (apply up_mono; lia).
  pose proof (up_le i ltac:(lia)) as H1. pose proof (up_step i ltac:(lia)) as H2.
  split; [apply lex_trans with (e (i + 1)); assumption|].
  intro E. rewrite <- E in M. apply H2. apply lex_antisym; assumption.
Qed.

Lemma junction1 : 4 <= k -> 0 < cross (e (L - 2)) (e (L - 1)) (e L).
Proof.
  intros Hk.
  assert (Ge : 0 <= cross (e (L - 2)) (e (L - 1)) (e L)).
  { replace (L - 1) with (L - 2 + 1) by lia. apply low_left; [lia | apply HS; lia]. }
  destruct (Z.eq_dec (cross (e (L - 2)) (e (L - 1)) (e L)) 0) as [Z0 | Z0]; [|lia].
  exfalso.
  assert (All : forall p, S p -> cross (e (L - 2)) (e (L - 1)) p = 0).
  { intros p Hp. apply geo_coll with (e L).
    - replace (L - 1) with (L - 2 + 1) by lia. apply low_le; lia.
    - replace (L - 1) with (L - 2 + 1) by lia. apply low_step; lia.
    - replace L with (L - 1 + 1) at 1 by lia. apply up_le; lia.
    - intro E. apply (up_step (L - 1)); [lia|]. replace (L - 1 + 1) with L by lia.
      symmetry; exact E.
    - exact Z0.
    - replace (L - 1) with (L - 2 + 1) by lia. apply low_left; [lia | exact Hp].
    - replace L with (L - 1 + 1) at 2 by lia. apply up_left; [lia | exact Hp]. }
  destruct (Z.eq_dec L 2) as [L2 | L2].
  - pose proof (up_cvx (L - 1) ltac:(lia) ltac:(lia)) as C.
    replace (L - 1 + 1) with L in C by lia. replace (L - 1 + 2) with (L + 1) in C by lia.
    rewrite (geo_col3 (e (L - 2)) (e (L - 1)) (e L) (e (L + 1))) in C; [lia | | |].
    + replace (L - 1) with (L - 2 + 1) by lia. apply low_step; lia.
    + apply All, HS; lia.
    + apply All, HS; lia.
  - pose proof (low_cvx (L - 3) ltac:(lia) ltac:(lia)) as C.
    replace (L - 3 + 1) with (L - 2) in C by lia. replace (L - 3 + 2) with (L - 1) in C by lia.
    rewrite cross_cyc, All in C; [lia | apply HS; lia].
Qed.

Lemma junction2 : 4 <= k -> 0 < cross (e (k - 2)) (e 0) (e 1).
Proof.
  intros Hk.
  assert (Ge : 0 <= cross (e (k - 2)) (e 0) (e 1)).
  { rewrite <- Hend. replace (k - 1) with (k - 2 + 1) by lia.
    apply up_left; [lia | apply HS; lia]. }
  destruct (Z.eq_dec (cross (e (k - 2)) (e 0) (e 1)) 0) as [Z0 | Z0]; [|lia].
  exfalso.
  assert (Hs : e (k - 2) <> e 0).
  { rewrite <- Hend. replace (k - 1) with (k - 2 + 1) by lia. apply up_step; lia. }
  assert (All : forall p, S p -> cross (e (k - 2)) (e 0) p = 0).
  { intros p Hp. rewrite <- (cross_neg (e (k - 2)) (e 0) p).
    apply geo_coll with (negp (e 1)).
    - apply lex_neg. rewrite <- Hend. replace (k - 1) with (k - 2 + 1) by lia.
      apply up_le; lia.
    - intro E. apply Hs. apply negp_inj. exact E.
    - apply lex_neg. replace 1 with (0 + 1) by lia. apply low_le; lia.
    - intro E. apply (low_step 0); [lia|]. symmetry. apply negp_inj. exact E.
    - rewrite cross_neg. exact Z0.
    - rewrite cross_neg. rewrite <- Hend. replace (k - 1) with (k - 2 + 1) by lia.
      apply up_left; [lia | exact Hp].
    - rewrite cross_neg. replace 1 with (0 + 1) by lia. apply low_left; [lia | exact Hp]. }
  destruct (Z.eq_dec k (L + 1)) as [K2 | K2].
  - pose proof (low_cvx 0 ltac:(lia) ltac:(lia)) as C. simpl in C.
    rewrite (geo_col3 (e (k - 2)) (e 0) (e 1) (e 2)) in C; [lia | exact Hs | |].
    + apply All, HS; lia.
    + apply All, HS; lia.
  - pose proof (up_cvx (k - 3) ltac:(lia) ltac:(lia)) as C.
    replace (k - 3 + 1) with (k - 2) in C by lia. replace (k - 3 + 2) with (k - 1) in C by lia.
    rewrite cross_cyc, Hend, All in C; [lia | apply HS; lia].
Qed.

Lemma cvx_full : 4 <= k -> forall j, 0 <= j <= k - 3 ->
  0 < cross (e j) (e (j + 1)) (e (j + 2)).
Proof.
  intros Hk j Hj.
  destruct (Z.le_gt_cases (j + 2) (L - 1)); [apply low_cvx; lia|].
  destruct (Z.eq_dec j (L - 2)) as [E | E].
  - subst j. replace (L - 2 + 1) with (L - 1) by lia. replace (L - 2 + 2) with L by lia.
    apply junction1; exact Hk.
  - apply up_cvx; lia.
Qed.

Lemma poly_nodup : forall i j, 0 <= i < j -> j <= k - 2 -> e i <> e j.
Proof.
  intros i j Hi Hj.
  destruct (Z.le_gt_cases j (L - 1)); [apply low_strict; lia|].
  destruct (Z.le_gt_cases (L - 1) i); [apply up_strict; lia|].
  destruct (Z.eq_dec i 0) as [I0 | I0].
  - subst i. rewrite <- Hend. intro E. apply (proj2 (up_strict j (k - 1) ltac:(lia) ltac:(lia))).
    symmetry; exact E.
  - intro E. apply (geo_nodup (e i) (e (i + 1)) (e (j + 1)) (e (i - 1))).
    + apply low_le; lia.
    + apply low_step; lia.
    + rewrite E. apply up_le; lia.
    + rewrite E. intro F. apply (up_step j); [lia|]. symmetry; exact F.
    + rewrite E. apply up_left; [lia | apply HS; lia].
    + apply low_left; [lia | apply HS; lia].
    + rewrite E. apply up_left; [lia | apply HS; lia].
    + pose proof (low_cvx (i - 1) ltac:(lia) ltac:(lia)) as C.
      replace (i - 1 + 1) with i in C by lia. replace (i - 1 + 2) with (i + 1) in C by lia.
      exact C.
Qed.

Lemma poly_seg : k = 3 -> forall p, S p -> on_segment (e 0) (e 1) p.
Proof.
  intros Hk p Hp.
  assert (L2 : L = 2) by lia.
  apply geo_seg.
  - apply (ch_bot _ _ _ _ Hlow); exact Hp.
  - replace 1 with (L - 1) by lia. apply (ch_top _ _ _ _ Hlow); exact Hp.
  - pose proof (low_left 0 p ltac:(lia) Hp) as C1.
    pose proof (up_left 1 p ltac:(lia) Hp) as C2.
    replace (1 + 1) with (k - 1) in C2 by lia. rewrite Hend, cross_swap in C2.
    simpl in C1. lia.
Qed.

End Polygon.

(* ------------------------------------------------------------------ *)
(* Uint63 / PArray plumbing                                            *)
(* ------------------------------------------------------------------ *)

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma max_length_val : (φ PArray.max_length) = 4194303%Z.
Proof. reflexivity. Qed.

Lemma alength_set : forall (t : array int) (i : int) (b : int),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set int t i b). Qed.

Lemma alength_make : forall (n : int) (b : int),
  PArray.length (PArray.make n b)
  = if n <=? PArray.max_length then n else PArray.max_length.
Proof. intros n b. exact (length_make int n b). Qed.

Lemma alength_make_small : forall (n : int) (b : int),
  ((φ n) <= 4194303)%Z -> PArray.length (PArray.make n b) = n.
Proof.
  intros n b H. rewrite alength_make.
  replace (n <=? PArray.max_length) with true; [reflexivity|].
  symmetry. rewrite leb_spec, max_length_val. exact H.
Qed.

Lemma aget_make : forall (n i : int) (b : int), (PArray.make n b).[i] = b.
Proof. intros n i b. exact (get_make int b n i). Qed.

Lemma aget_set_same : forall (t : array int) (i : int) (b : int),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same int t i b H). Qed.

Lemma aget_set_other : forall (t : array int) (i j : int) (b : int),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other int t i j b H). Qed.

Lemma aget_oob : forall (t : array int) (i : int),
  (i <? PArray.length t) = false -> t.[i] = default t.
Proof. intros t i H. exact (get_out_of_bounds int t i H). Qed.

Lemma adefault_set : forall (t : array int) (i : int) (b : int),
  default t.[i <- b] = default t.
Proof. intros t i b. exact (default_set int t i b). Qed.

(* reading at a Z position *)
Definition rd (a : array int) (p : Z) : int := a.[of_Z p].

Lemma rd_phi : forall (a : array int) (i : int), rd a (φ i) = a.[i].
Proof. intros a i. unfold rd. rewrite of_to_Z. reflexivity. Qed.

Lemma phi_of_Z : forall p : Z, (0 <= p < wB)%Z -> (φ (of_Z p)) = p.
Proof. intros p Hp. rewrite of_Z_spec. apply Z.mod_small. exact Hp. Qed.

Lemma rd_set_same : forall (a : array int) (i v : int),
  ((φ i) < (φ (PArray.length a)))%Z -> rd a.[i <- v] (φ i) = v.
Proof.
  intros a i v H. rewrite rd_phi. apply (get_set_same int a i v).
  rewrite ltb_spec. exact H.
Qed.

Lemma rd_set_other : forall (a : array int) (i v : int) (p : Z),
  (0 <= p < wB)%Z -> p <> (φ i) -> rd a.[i <- v] p = rd a p.
Proof.
  intros a i v p Hp Hne. unfold rd. apply (get_set_other int a i (of_Z p) v).
  intro E. apply Hne. rewrite E. symmetry. apply phi_of_Z. exact Hp.
Qed.

Lemma rd_make : forall (n : int) (b : int) (p : Z), rd (PArray.make n b) p = b.
Proof. intros. unfold rd. apply aget_make. Qed.

Lemma sint_ltb : forall a b : int, Sint63.ltb a b = true <-> (Sint63.to_Z a < Sint63.to_Z b)%Z.
Proof. intros a b. rewrite Sint63.ltb_spec. rewrite Z.compare_lt_iff. reflexivity. Qed.

Lemma sint_leb : forall a b : int, Sint63.leb a b = true <-> (Sint63.to_Z a <= Sint63.to_Z b)%Z.
Proof. intros a b. rewrite Sint63.leb_spec. rewrite Z.compare_le_iff. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The machine side                                                    *)
(* ------------------------------------------------------------------ *)

Section Machine.
Local Open Scope Z_scope.

Variables x y : array int.
Variable n : int.
Hypothesis Hn : 1 <= (φ n) <= 10000.

Definition Pt (a : int) : point := (Sint63.to_Z x.[a], Sint63.to_Z y.[a]).

Definition le_i (a b : int) : Prop := lex (Pt a) (Pt b).

Lemma le_pt_spec : forall a b, le_pt x y a b = true <-> le_i a b.
Proof.
  intros a b. unfold le_pt, le_i, lex, Pt; simpl.
  destruct (Sint63.ltb x.[a] x.[b]) eqn:E1.
  - rewrite sint_ltb in E1. split; [lia | reflexivity].
  - assert (E1' : ~ Sint63.to_Z x.[a] < Sint63.to_Z x.[b])
      by (rewrite <- sint_ltb; rewrite E1; discriminate).
    destruct ((x.[a] =? x.[b])%uint63) eqn:E2.
    + rewrite eqb_spec in E2. rewrite E2. rewrite sint_leb. lia.
    + rewrite eqb_false_spec in E2.
      assert (Sint63.to_Z x.[a] <> Sint63.to_Z x.[b])
        by (intro F; apply E2; apply Sint63.to_Z_inj; exact F).
      split; [discriminate | lia].
Qed.

Lemma le_pt_false : forall a b, le_pt x y a b = false -> le_i b a.
Proof.
  intros a b H. unfold le_i. destruct (lex_total (Pt a) (Pt b)) as [L | L]; [|exact L].
  apply le_pt_spec in L. rewrite L in H. discriminate.
Qed.

(* every cell is an index of an input point *)
Definition valid (a : array int) : Prop := forall j : int, (φ (a.[j])) < (φ n).

Lemma valid_rd : forall a p, valid a -> (φ (rd a p)) < (φ n).
Proof. intros a p H. apply H. Qed.

Lemma valid_set : forall a i v, valid a -> (φ v) < (φ n) -> valid a.[i <- v].
Proof.
  intros a i v Ha Hv j. destruct (Uint63.eqb i j) eqn:E.
  - rewrite eqb_spec in E. subst j.
    destruct ((i <? PArray.length a)%uint63) eqn:L.
    + rewrite (aget_set_same a i v L). exact Hv.
    + rewrite (aget_oob a.[i <- v] i) by (rewrite alength_set; exact L).
      rewrite adefault_set.
      rewrite <- (aget_oob a i L). apply Ha.
  - rewrite eqb_false_spec in E. rewrite (aget_set_other a i j v E). apply Ha.
Qed.

Lemma valid_make : forall m, valid (PArray.make m 0%uint63).
Proof. intros m j. rewrite aget_make. change (φ 0) with 0. lia. Qed.

(* ---------------- sorting ---------------- *)

Definition sorted_rng (a : array int) (lo hi : Z) : Prop :=
  forall p, lo <= p -> p + 1 < hi -> le_i (rd a p) (rd a (p + 1)).

Record MI (src dst0 : array int) (lo mid hi : Z) (i j k : int) (dst : array int) : Prop := {
  mi_i : lo <= (φ i) <= mid;
  mi_j : mid <= (φ j) <= hi;
  mi_k : (φ k) = (φ i) + (φ j) - mid;
  mi_len : PArray.length dst = PArray.length dst0;
  mi_out : forall p, 0 <= p < wB -> (p < lo \/ hi <= p) -> rd dst p = rd dst0 p;
  mi_sorted : sorted_rng dst lo (φ k);
  mi_lasti : lo < (φ k) -> (φ i) < mid -> le_i (rd dst ((φ k) - 1)) (rd src (φ i));
  mi_lastj : lo < (φ k) -> (φ j) < hi -> le_i (rd dst ((φ k) - 1)) (rd src (φ j));
  mi_incl : forall p, (lo <= p < (φ i) \/ mid <= p < (φ j)) ->
              exists p', lo <= p' < (φ k) /\ rd dst p' = rd src p;
  mi_valid : valid dst;
}.

Lemma take_left_true : forall src mid hi i j,
  take_left x y src mid hi i j = true ->
  (φ i) < (φ mid) /\ ((φ j) < (φ hi) -> le_i (rd src (φ i)) (rd src (φ j))).
Proof.
  intros src mid hi i j H. unfold take_left in H.
  destruct ((i <? mid)%uint63) eqn:E1; [|discriminate]. rewrite ltb_spec in E1.
  split; [exact E1|]. intros Hj.
  assert (E2 : (j <? hi)%uint63 = true) by (rewrite ltb_spec; exact Hj).
  rewrite E2 in H. rewrite !rd_phi. apply le_pt_spec. exact H.
Qed.

Lemma take_left_false : forall src mid hi i j,
  take_left x y src mid hi i j = false ->
  (φ mid) <= (φ i) \/
  ((φ i) < (φ mid) /\ (φ j) < (φ hi) /\ le_i (rd src (φ j)) (rd src (φ i))).
Proof.
  intros src mid hi i j H. unfold take_left in H.
  destruct ((i <? mid)%uint63) eqn:E1; [| left; rewrite <- Bool.not_true_iff_false, ltb_spec in E1; lia].
  rewrite ltb_spec in E1. right. split; [exact E1|].
  destruct ((j <? hi)%uint63) eqn:E2; [|discriminate]. rewrite ltb_spec in E2.
  split; [exact E2|]. rewrite !rd_phi. apply le_pt_false. exact H.
Qed.

Lemma merge_correct : forall (src dst0 : array int) (lo mid hi : int),
  (φ lo) <= (φ mid) <= (φ hi) -> (φ hi) <= (φ (PArray.length dst0)) -> (φ hi) <= 10000 ->
  sorted_rng src (φ lo) (φ mid) -> sorted_rng src (φ mid) (φ hi) -> valid src ->
  forall z i j k dst (H : Acc (Zwf 0) (gap hi k)), gap hi k = z ->
  MI src dst0 (φ lo) (φ mid) (φ hi) i j k dst ->
  exists i' j', MI src dst0 (φ lo) (φ mid) (φ hi) i' j' hi
                  (merge x y src mid hi i j k dst H).
Proof.
  intros src dst0 lo mid hi Hlmh Hhl Hh10 Hs1 Hs2 Hvs z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i j k dst H Hz Hmi.
  pose proof (mi_i _ _ _ _ _ _ _ _ _ Hmi) as Hi.
  pose proof (mi_j _ _ _ _ _ _ _ _ _ Hmi) as Hj.
  pose proof (mi_k _ _ _ _ _ _ _ _ _ Hmi) as Hk.
  pose proof (mi_len _ _ _ _ _ _ _ _ _ Hmi) as Hlen.
  destruct H as [H]. simpl.
  destruct (bdec (k <? hi)%uint63) as [Hkh | Hkh].
  - pose proof Hkh as Hkh'. rewrite ltb_spec in Hkh'.
    assert (Hk1 : (φ (k + 1)) = (φ k) + 1) by sia.
    assert (HkL : (φ k) < (φ (PArray.length dst))) by (rewrite Hlen; lia).
    pose proof (to_Z_bounded k) as Bk.
    destruct (take_left x y src mid hi i j) eqn:Et.
    + destruct (take_left_true _ _ _ _ _ Et) as [Him Hle].
      assert (Hi1 : (φ (i + 1)) = (φ i) + 1) by sia.
      eapply IH; [ | reflexivity | ].
      { rewrite <- Hz. apply dec_step. exact Hkh. }
      rewrite <- !rd_phi.
      constructor.
      * lia.
      * exact Hj.
      * lia.
      * rewrite alength_set. exact Hlen.
      * intros p Hp Hp'. rewrite rd_set_other by lia.
        apply (mi_out _ _ _ _ _ _ _ _ _ Hmi); assumption.
      * intros p Hp1 Hp2. rewrite Hk1 in Hp2.
        destruct (Z.eq_dec (p + 1) (φ k)) as [E | E].
        -- rewrite (rd_set_other dst k _ p) by (rewrite ?wB_val; lia).
           rewrite E, rd_set_same by exact HkL.
           replace p with ((φ k) - 1) by lia.
           apply (mi_lasti _ _ _ _ _ _ _ _ _ Hmi); lia.
        -- rewrite (rd_set_other dst k _ p) by (rewrite ?wB_val; lia).
           rewrite (rd_set_other dst k _ (p + 1)) by (rewrite ?wB_val; lia).
           apply (mi_sorted _ _ _ _ _ _ _ _ _ Hmi); lia.
      * intros _ Hi'. rewrite Hk1. replace ((φ k) + 1 - 1) with (φ k) by lia.
        rewrite rd_set_same by exact HkL. rewrite Hi1.
        apply Hs1; lia.
      * intros _ Hj'. rewrite Hk1. replace ((φ k) + 1 - 1) with (φ k) by lia.
        rewrite rd_set_same by exact HkL. apply Hle. exact Hj'.
      * intros p Hp. rewrite Hi1 in Hp.
        destruct (Z.eq_dec p (φ i)) as [E | E].
        -- exists (φ k). split; [lia|]. rewrite rd_set_same by exact HkL.
           rewrite E. reflexivity.
        -- destruct (mi_incl _ _ _ _ _ _ _ _ _ Hmi p ltac:(lia)) as (p' & Hp' & Ep').
           exists p'. split; [lia|]. rewrite rd_set_other by (rewrite ?wB_val; lia). exact Ep'.
      * apply valid_set; [apply (mi_valid _ _ _ _ _ _ _ _ _ Hmi) | rewrite rd_phi; apply Hvs].
    + assert (Hjh : (φ j) < (φ hi) /\
                ((φ i) < (φ mid) -> le_i (rd src (φ j)) (rd src (φ i)))).
      { destruct (take_left_false _ _ _ _ _ Et) as [F | (F1 & F2 & F3)].
        - split; [lia | intros; lia].
        - split; [exact F2 | intros; exact F3]. }
      destruct Hjh as [Hjh Hle].
      assert (Hj1 : (φ (j + 1)) = (φ j) + 1) by sia.
      eapply IH; [ | reflexivity | ].
      { rewrite <- Hz. apply dec_step. exact Hkh. }
      rewrite <- !rd_phi.
      constructor.
      * exact Hi.
      * lia.
      * lia.
      * rewrite alength_set. exact Hlen.
      * intros p Hp Hp'. rewrite rd_set_other by lia.
        apply (mi_out _ _ _ _ _ _ _ _ _ Hmi); assumption.
      * intros p Hp1 Hp2. rewrite Hk1 in Hp2.
        destruct (Z.eq_dec (p + 1) (φ k)) as [E | E].
        -- rewrite (rd_set_other dst k _ p) by (rewrite ?wB_val; lia).
           rewrite E, rd_set_same by exact HkL.
           replace p with ((φ k) - 1) by lia.
           apply (mi_lastj _ _ _ _ _ _ _ _ _ Hmi); lia.
        -- rewrite (rd_set_other dst k _ p) by (rewrite ?wB_val; lia).
           rewrite (rd_set_other dst k _ (p + 1)) by (rewrite ?wB_val; lia).
           apply (mi_sorted _ _ _ _ _ _ _ _ _ Hmi); lia.
      * intros _ Hi'. rewrite Hk1. replace ((φ k) + 1 - 1) with (φ k) by lia.
        rewrite rd_set_same by exact HkL. apply Hle. exact Hi'.
      * intros _ Hj'. rewrite Hk1. replace ((φ k) + 1 - 1) with (φ k) by lia.
        rewrite rd_set_same by exact HkL. rewrite Hj1.
        apply Hs2; lia.
      * intros p Hp. rewrite Hj1 in Hp.
        destruct (Z.eq_dec p (φ j)) as [E | E].
        -- exists (φ k). split; [lia|]. rewrite rd_set_same by exact HkL.
           rewrite E. reflexivity.
        -- destruct (mi_incl _ _ _ _ _ _ _ _ _ Hmi p ltac:(lia)) as (p' & Hp' & Ep').
           exists p'. split; [lia|]. rewrite rd_set_other by (rewrite ?wB_val; lia). exact Ep'.
      * apply valid_set; [apply (mi_valid _ _ _ _ _ _ _ _ _ Hmi) | rewrite rd_phi; apply Hvs].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hkh.
    assert (k = hi) by (apply to_Z_inj; lia). subst k.
    exists i, j. exact Hmi.
Qed.

Lemma min_i_spec : forall a b : int, (φ (min_i a b)) = Z.min (φ a) (φ b).
Proof.
  intros a b. unfold min_i. destruct (a <? b)%uint63 eqn:E.
  - rewrite ltb_spec in E. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in E. lia.
Qed.

Lemma mod_ne : forall a m r, 0 < m -> a mod m = 0 -> a < r < a + m -> r mod m <> 0.
Proof.
  intros a m r Hm Ha Hr.
  pose proof (Z.div_mod a m ltac:(lia)) as Da. rewrite Ha, Z.add_0_r in Da.
  intro E. assert (E' : r - a = r mod m) by (apply Z.mod_unique with (a / m); lia). lia.
Qed.

Lemma mod_half : forall a m, 0 < m -> a mod (2 * m) = 0 -> a mod m = 0.
Proof.
  intros a m Hm H. apply Z.mod_divide in H; [|lia]. destruct H as [q Hq].
  apply Z.mod_divide; [lia|]. exists (2 * q). lia.
Qed.

Lemma mod_add_self : forall a m, 0 < m -> a mod m = 0 -> (a + m) mod m = 0.
Proof.
  intros a m Hm H. apply Z.mod_divide in H; [|lia]. destruct H as [q Hq].
  apply Z.mod_divide; [lia|]. exists (q + 1). lia.
Qed.

Definition wsorted (a : array int) (w : Z) : Prop :=
  forall p, 0 <= p -> p + 1 < (φ n) -> (p + 1) mod w <> 0 -> le_i (rd a p) (rd a (p + 1)).

Record PI (src dst0 : array int) (w lo : int) (dst : array int) : Prop := {
  pi_lo : (φ lo) <= (φ n);
  pi_mod : (φ lo) mod (2 * (φ w)) = 0 \/ (φ lo) = (φ n);
  pi_len : PArray.length dst = PArray.length dst0;
  pi_sorted : forall p, 0 <= p -> p + 1 < (φ lo) -> (p + 1) mod (2 * (φ w)) <> 0 ->
                le_i (rd dst p) (rd dst (p + 1));
  pi_incl : forall p, 0 <= p < (φ lo) -> exists p', 0 <= p' < (φ lo) /\ rd dst p' = rd src p;
  pi_valid : valid dst;
}.

Lemma pass_correct : forall (src dst0 : array int) (w : int),
  1 <= (φ w) < (φ n) -> (φ n) <= (φ (PArray.length dst0)) ->
  wsorted src (φ w) -> valid src ->
  forall z lo dst (H : Acc (Zwf 0) (gap n lo)), gap n lo = z ->
  PI src dst0 w lo dst -> PI src dst0 w n (pass x y src w n lo dst H).
Proof.
  intros src dst0 w Hw Hl0 Hws Hvs z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros lo dst H Hz Hpi.
  pose proof (pi_lo _ _ _ _ _ Hpi) as Hlo.
  pose proof (to_Z_bounded lo) as Blo.
  destruct H as [H]. simpl.
  assert (Hlw : (φ (lo + w + w)) = (φ lo) + 2 * (φ w)) by sia.
  assert (Hlw1 : (φ (lo + w)) = (φ lo) + (φ w)) by sia.
  set (hi := min_i (lo + w + w) n).
  set (mid := min_i (lo + w) n).
  assert (Hhi : (φ hi) = Z.min ((φ lo) + 2 * (φ w)) (φ n)) by (unfold hi; rewrite min_i_spec, Hlw; reflexivity).
  assert (Hmid : (φ mid) = Z.min ((φ lo) + (φ w)) (φ n)) by (unfold mid; rewrite min_i_spec, Hlw1; reflexivity).
  destruct (bdec (lo <? hi)%uint63) as [Hc | Hc].
  - pose proof Hc as Hc'. rewrite ltb_spec in Hc'.
    assert (Hlon : (φ lo) < (φ n)) by lia.
    assert (Hmod2 : (φ lo) mod (2 * (φ w)) = 0) by (destruct (pi_mod _ _ _ _ _ Hpi); lia).
    assert (Hmod1 : (φ lo) mod (φ w) = 0) by (apply mod_half; lia).
    assert (Hlen : PArray.length dst = PArray.length dst0) by apply (pi_len _ _ _ _ _ Hpi).
    assert (Hs1 : sorted_rng src (φ lo) (φ mid)).
    { intros p Hp1 Hp2. apply Hws; [lia | lia |].
      apply (mod_ne (φ lo)); lia. }
    assert (Hs2 : sorted_rng src (φ mid) (φ hi)).
    { intros p Hp1 Hp2. apply Hws; [lia | lia |].
      assert (Em : (φ mid) = (φ lo) + (φ w)) by lia.
      apply (mod_ne (φ mid)); [lia | rewrite Em; apply mod_add_self; lia | lia]. }
    assert (Hm0 : MI src dst (φ lo) (φ mid) (φ hi) lo mid lo dst).
    { constructor.
      - lia.
      - lia.
      - lia.
      - reflexivity.
      - intros; reflexivity.
      - intros p Hp1 Hp2. lia.
      - intros F _. lia.
      - intros F _. lia.
      - intros p Hp. lia.
      - apply (pi_valid _ _ _ _ _ Hpi). }
    destruct (merge_correct src dst lo mid hi ltac:(lia)
                ltac:(rewrite Hlen; lia) ltac:(lia) Hs1 Hs2 Hvs
                _ lo mid lo dst (Zwf_well_founded 0 (gap hi lo)) eq_refl Hm0)
      as (i' & j' & Hmi).
    set (r := merge x y src mid hi lo mid lo dst (Zwf_well_founded 0 (gap hi lo))) in *.
    pose proof (mi_i _ _ _ _ _ _ _ _ _ Hmi) as Hi'.
    pose proof (mi_j _ _ _ _ _ _ _ _ _ Hmi) as Hj'.
    pose proof (mi_k _ _ _ _ _ _ _ _ _ Hmi) as Hk'.
    eapply IH; [ | reflexivity | ].
    { rewrite <- Hz. apply pass_dec. exact Hc. }
    fold hi. constructor.
    + lia.
    + destruct (Z.lt_ge_cases ((φ lo) + 2 * (φ w)) (φ n)) as [E | E].
      * left. replace (φ hi) with ((φ lo) + 2 * (φ w)) by lia.
        replace ((φ lo) + 2 * (φ w)) with ((φ lo) + 2 * (φ w)) by lia.
        apply mod_add_self; lia.
      * right. lia.
    + rewrite (mi_len _ _ _ _ _ _ _ _ _ Hmi). exact Hlen.
    + intros p Hp1 Hp2 Hp3.
      destruct (Z.lt_ge_cases (p + 1) (φ lo)) as [E | E].
      * rewrite !(mi_out _ _ _ _ _ _ _ _ _ Hmi) by (rewrite ?wB_val; lia).
        apply (pi_sorted _ _ _ _ _ Hpi); assumption.
      * destruct (Z.eq_dec (p + 1) (φ lo)) as [E' | E']; [rewrite E' in Hp3; contradiction|].
        apply (mi_sorted _ _ _ _ _ _ _ _ _ Hmi); lia.
    + intros p Hp.
      destruct (Z.lt_ge_cases p (φ lo)) as [E | E].
      * destruct (pi_incl _ _ _ _ _ Hpi p ltac:(lia)) as (p' & Hp' & Ep').
        exists p'. split; [lia|].
        rewrite (mi_out _ _ _ _ _ _ _ _ _ Hmi) by (rewrite ?wB_val; lia). exact Ep'.
      * destruct (mi_incl _ _ _ _ _ _ _ _ _ Hmi p ltac:(lia)) as (p' & Hp' & Ep').
        exists p'. split; [lia | exact Ep'].
    + apply (mi_valid _ _ _ _ _ _ _ _ _ Hmi).
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hc.
    assert (lo = n) by (apply to_Z_inj; lia). subst lo. exact Hpi.
Qed.

Definition covers (a : array int) : Prop :=
  forall i : int, (φ i) < (φ n) -> exists p, 0 <= p < (φ n) /\ rd a p = i.

Record SI (w : int) (src dst : array int) : Prop := {
  si_ls : (φ (PArray.length src)) = (φ n);
  si_ld : (φ (PArray.length dst)) = (φ n);
  si_w : 1 <= (φ w);
  si_sorted : wsorted src (φ w);
  si_covers : covers src;
  si_vs : valid src;
  si_vd : valid dst;
}.

Lemma sort_correct : forall z w src dst (H : Acc (Zwf 0) (mz n w)), mz n w = z ->
  SI w src dst ->
  let r := sortl x y n w src dst H in
  (φ (PArray.length r)) = (φ n) /\ sorted_rng r 0 (φ n) /\ covers r /\ valid r.
Proof.
  intro z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros w src dst H Hz Hsi.
  pose proof (si_w _ _ _ Hsi) as Hw.
  destruct H as [H]. simpl.
  destruct (bdec ((w <? n) && (w <? w + w))%uint63) as [Hc | Hc].
  - pose proof Hc as Hc'. apply andb_prop in Hc'. destruct Hc' as [Hc1 _].
    rewrite ltb_spec in Hc1.
    assert (Hww : (φ (w + w)) = 2 * (φ w)) by sia.
    assert (Hp0 : PI src dst w 0 dst).
    { constructor; change (φ 0) with 0.
      - lia.
      - left. apply Z.mod_0_l. lia.
      - reflexivity.
      - intros p Hp1 Hp2. lia.
      - intros p Hp. lia.
      - apply (si_vd _ _ _ Hsi). }
    pose proof (pass_correct src dst w ltac:(lia)
                  ltac:(rewrite (si_ld _ _ _ Hsi); lia)
                  (si_sorted _ _ _ Hsi) (si_vs _ _ _ Hsi)
                  _ 0 dst (Zwf_well_founded 0 (gap n 0)) eq_refl Hp0) as Hpi.
    eapply IH; [ | reflexivity | ].
    { rewrite <- Hz. apply sort_dec. exact Hc. }
    constructor.
    + rewrite (pi_len _ _ _ _ _ Hpi). apply (si_ld _ _ _ Hsi).
    + apply (si_ls _ _ _ Hsi).
    + lia.
    + intros p Hp1 Hp2 Hp3. apply (pi_sorted _ _ _ _ _ Hpi); [lia | lia | rewrite <- Hww; exact Hp3].
    + intros i Hi. destruct (si_covers _ _ _ Hsi i Hi) as (p & Hp & Ep).
      destruct (pi_incl _ _ _ _ _ Hpi p Hp) as (p' & Hp' & Ep').
      exists p'. split; [exact Hp' | rewrite Ep'; exact Ep].
    + apply (pi_valid _ _ _ _ _ Hpi).
    + apply (si_vs _ _ _ Hsi).
  - assert (Hwn : (φ n) <= (φ w)).
    { destruct (Z.lt_ge_cases (φ w) (φ n)) as [E | E]; [|exact E].
      exfalso. assert (Hww : (φ (w + w)) = 2 * (φ w)) by sia.
      assert (E1 : (w <? n)%uint63 = true) by (rewrite ltb_spec; exact E).
      assert (E2 : (w <? w + w)%uint63 = true) by (rewrite ltb_spec; lia).
      rewrite E1, E2 in Hc. discriminate. }
    split; [apply (si_ls _ _ _ Hsi)|]. split; [|split; [apply (si_covers _ _ _ Hsi) | apply (si_vs _ _ _ Hsi)]].
    intros p Hp1 Hp2. apply (si_sorted _ _ _ Hsi); [lia | lia |].
    rewrite Z.mod_small by lia. lia.
Qed.

Lemma init_correct : forall z i a (H : Acc (Zwf 0) (gap n i)), gap n i = z ->
  (φ i) <= (φ n) -> (φ (PArray.length a)) = (φ n) ->
  (forall p, 0 <= p < (φ i) -> rd a p = of_Z p) -> valid a ->
  let r := initl n i a H in
  (φ (PArray.length r)) = (φ n) /\ (forall p, 0 <= p < (φ n) -> rd r p = of_Z p) /\ valid r.
Proof.
  intro z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i a H Hz Hi Hl Hc Hv.
  destruct H as [H]. simpl.
  destruct (bdec (i <? n)%uint63) as [Hc' | Hc'].
  - pose proof Hc' as Hc''. rewrite ltb_spec in Hc''.
    assert (Hi1 : (φ (i + 1)) = (φ i) + 1) by sia.
    eapply IH; [ | reflexivity | | | | ].
    + rewrite <- Hz. apply dec_step. exact Hc'.
    + lia.
    + rewrite alength_set. exact Hl.
    + intros p Hp. rewrite Hi1 in Hp. destruct (Z.eq_dec p (φ i)) as [E | E].
      * subst p. rewrite rd_set_same by lia. symmetry. apply of_to_Z.
      * rewrite rd_set_other by (rewrite ?wB_val; lia). apply Hc. lia.
    + apply valid_set; [exact Hv | exact Hc''].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hc'.
    split; [exact Hl|]. split; [intros p Hp; apply Hc; lia | exact Hv].
Qed.

Lemma msort_correct :
  let ord := msort x y n in
  (φ (PArray.length ord)) = (φ n) /\ sorted_rng ord 0 (φ n) /\ covers ord /\ valid ord.
Proof.
  unfold msort.
  assert (Hm : (φ (PArray.length (PArray.make n 0%uint63))) = (φ n))
    by (rewrite alength_make_small by lia; reflexivity).
  destruct (init_correct _ 0 (PArray.make n 0%uint63) (Zwf_well_founded 0 (gap n 0)) eq_refl
              ltac:(change (φ 0) with 0; lia) Hm
              ltac:(intros p Hp; change (φ 0) with 0 in Hp; lia) (valid_make n))
    as (Hl & Hc & Hv).
  apply (sort_correct _ 1 _ _ (Zwf_well_founded 0 (mz n 1)) eq_refl).
  constructor.
  - exact Hl.
  - exact Hm.
  - change (φ 1) with 1. lia.
  - intros p _ _ Hp. change (φ 1) with 1 in Hp. rewrite Z.mod_1_r in Hp. contradiction.
  - intros i Hi. exists (φ i). split; [pose proof (to_Z_bounded i); lia|].
    rewrite Hc by (pose proof (to_Z_bounded i); lia). apply of_to_Z.
  - exact Hv.
  - apply valid_make.
Qed.

End Machine.

(* ------------------------------------------------------------------ *)
(* The two scans                                                       *)
(* ------------------------------------------------------------------ *)

Lemma sint_min : Sint63.to_Z Sint63.min_int = (-4611686018427387904)%Z.
Proof. reflexivity. Qed.

Lemma sint_max : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z.
Proof. reflexivity. Qed.

Lemma sub_ex : forall a b : int,
  (- 1000000000 <= Sint63.to_Z a <= 1000000000)%Z ->
  (- 1000000000 <= Sint63.to_Z b <= 1000000000)%Z ->
  Sint63.to_Z (a - b) = (Sint63.to_Z a - Sint63.to_Z b)%Z.
Proof. intros a b Ha Hb. apply Sint63.to_Z_sub. rewrite sint_min, sint_max. lia. Qed.

Lemma mul_ex : forall a b : int,
  (- 1000000000 <= Sint63.to_Z a <= 1000000000)%Z ->
  (- 1000000000 <= Sint63.to_Z b <= 1000000000)%Z ->
  Sint63.to_Z (a * b) = (Sint63.to_Z a * Sint63.to_Z b)%Z.
Proof. intros a b Ha Hb. apply Sint63.to_Z_mul. rewrite sint_min, sint_max. nia. Qed.

Lemma sub_big : forall a b : int,
  (- 1000000000000 <= Sint63.to_Z a <= 1000000000000)%Z ->
  (- 1000000000000 <= Sint63.to_Z b <= 1000000000000)%Z ->
  Sint63.to_Z (a - b) = (Sint63.to_Z a - Sint63.to_Z b)%Z.
Proof. intros a b Ha Hb. apply Sint63.to_Z_sub. rewrite sint_min, sint_max. lia. Qed.

Section Scan.
Local Open Scope Z_scope.

Variables x y : array int.
Variable n : int.
Hypothesis Hn : 1 <= (φ n) <= 10000.
Hypothesis Hcoord : forall a : int, (φ a) < (φ n) ->
  -10000 <= Sint63.to_Z x.[a] <= 10000 /\ -10000 <= Sint63.to_Z y.[a] <= 10000.

Local Notation P0 := (Pt x y).

Lemma cross_m_spec : forall a b c, (φ a) < (φ n) -> (φ b) < (φ n) -> (φ c) < (φ n) ->
  Sint63.to_Z (cross_m x y a b c) = cross (P0 a) (P0 b) (P0 c).
Proof.
  intros a b c Ha Hb Hc.
  destruct (Hcoord a Ha) as [Xa Ya]. destruct (Hcoord b Hb) as [Xb Yb].
  destruct (Hcoord c Hc) as [Xc Yc].
  unfold cross_m, cross, Pt; simpl.
  assert (E1 : Sint63.to_Z (x.[b] - x.[a]) = Sint63.to_Z x.[b] - Sint63.to_Z x.[a]) by (apply sub_ex; lia).
  assert (E2 : Sint63.to_Z (y.[c] - y.[a]) = Sint63.to_Z y.[c] - Sint63.to_Z y.[a]) by (apply sub_ex; lia).
  assert (E3 : Sint63.to_Z (y.[b] - y.[a]) = Sint63.to_Z y.[b] - Sint63.to_Z y.[a]) by (apply sub_ex; lia).
  assert (E4 : Sint63.to_Z (x.[c] - x.[a]) = Sint63.to_Z x.[c] - Sint63.to_Z x.[a]) by (apply sub_ex; lia).
  assert (E5 : Sint63.to_Z ((x.[b] - x.[a]) * (y.[c] - y.[a]))
             = Sint63.to_Z (x.[b] - x.[a]) * Sint63.to_Z (y.[c] - y.[a])) by (apply mul_ex; lia).
  assert (E6 : Sint63.to_Z ((y.[b] - y.[a]) * (x.[c] - x.[a]))
             = Sint63.to_Z (y.[b] - y.[a]) * Sint63.to_Z (x.[c] - x.[a])) by (apply mul_ex; lia).
  rewrite sub_big; rewrite ?E5, ?E6, ?E1, ?E2, ?E3, ?E4; [reflexivity | nia | nia].
Qed.

Section Pop.
Variable P : int -> point.
Hypothesis HP : forall a b c, (φ a) < (φ n) -> (φ b) < (φ n) -> (φ c) < (φ n) ->
  Sint63.to_Z (cross_m x y a b c) = cross (P a) (P b) (P c).

Lemma pop_correct : forall (st : array int) (lim q : int) (Pr : point -> Prop) (k0 : int),
  valid n st -> (φ q) < (φ n) -> 1 <= (φ lim) ->
  forall z k (H : Acc (Zwf 0) (φ k)), (φ k) = z -> (φ lim) <= (φ k) <= (φ k0) ->
  popinv (fun j => P (rd st j)) ((φ lim) - 1) ((φ k0) - 1) ((φ k) - 1) Pr (P q) ->
  let k' := pop x y st lim k q H in
  (φ lim) <= (φ k') <= (φ k0) /\
  popinv (fun j => P (rd st j)) ((φ lim) - 1) ((φ k0) - 1) ((φ k') - 1) Pr (P q) /\
  ((φ k') = (φ lim) \/ 0 < cross (P (rd st ((φ k') - 2))) (P (rd st ((φ k') - 1))) (P q)).
Proof.
  intros st lim q Pr k0 Hv Hq Hlim z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k H Hz Hk Hpi.
  destruct H as [H]. simpl.
  destruct (bdec ((lim <? k) && Sint63.leb (cross_m x y st.[k - 2] st.[k - 1] q) 0)%uint63)
    as [Hc | Hc].
  - pose proof Hc as Hc'. apply andb_prop in Hc'. destruct Hc' as [Hc1 Hc2].
    rewrite ltb_spec in Hc1. rewrite sint_leb in Hc2.
    assert (E2 : (φ (k - 2)) = (φ k) - 2) by sia.
    assert (E1 : (φ (k - 1)) = (φ k) - 1) by sia.
    rewrite <- (rd_phi st (k - 2)), <- (rd_phi st (k - 1)), E1, E2 in Hc2.
    rewrite HP in Hc2 by first [exact Hq | apply valid_rd; exact Hv].
    change (Sint63.to_Z 0) with 0 in Hc2.
    eapply IH; [ | reflexivity | lia | ].
    + rewrite <- Hz. unfold Zwf. lia.
    + rewrite E1. replace ((φ k) - 1 - 1) with ((φ k) - 1 - 1) by lia.
      apply popinv_step; [exact Hpi | lia |].
      replace ((φ k) - 1 - 1) with ((φ k) - 2) by lia. exact Hc2.
  - split; [exact Hk|]. split; [exact Hpi|].
    destruct (Z.eq_dec (φ k) (φ lim)) as [E | E]; [left; exact E | right].
    assert (Hc1 : (lim <? k)%uint63 = true) by (rewrite ltb_spec; lia).
    rewrite Hc1 in Hc. simpl in Hc.
    rewrite <- Bool.not_true_iff_false, sint_leb in Hc.
    assert (E2 : (φ (k - 2)) = (φ k) - 2) by sia.
    assert (E1 : (φ (k - 1)) = (φ k) - 1) by sia.
    rewrite <- (rd_phi st (k - 2)), <- (rd_phi st (k - 1)), E1, E2 in Hc.
    rewrite HP in Hc by first [exact Hq | apply valid_rd; exact Hv].
    change (Sint63.to_Z 0) with 0 in Hc. lia.
Qed.

End Pop.

Lemma HP0 : forall a b c, (φ a) < (φ n) -> (φ b) < (φ n) -> (φ c) < (φ n) ->
  Sint63.to_Z (cross_m x y a b c) = cross (P0 a) (P0 b) (P0 c).
Proof. exact cross_m_spec. Qed.

Lemma HP1 : forall a b c, (φ a) < (φ n) -> (φ b) < (φ n) -> (φ c) < (φ n) ->
  Sint63.to_Z (cross_m x y a b c)
  = cross ((fun i => negp (P0 i)) a) ((fun i => negp (P0 i)) b) ((fun i => negp (P0 i)) c).
Proof. intros. cbv beta. rewrite cross_neg. apply cross_m_spec; assumption. Qed.

Variable ord : array int.
Hypothesis Hord_len : (φ (PArray.length ord)) = (φ n).
Hypothesis Hord_sorted : sorted_rng x y ord 0 (φ n).
Hypothesis Hord_valid : valid n ord.

Lemma ord_mono : forall p1 p2, 0 <= p1 <= p2 -> p2 < (φ n) ->
  lex (P0 (rd ord p1)) (P0 (rd ord p2)).
Proof.
  intros p1 p2 H1 H2.
  apply (mono_of_steps (fun p => P0 (rd ord p)) 0 ((φ n) - 1)); [|lia|lia|lia].
  intros j Hj. apply Hord_sorted; lia.
Qed.

Definition PrL (m : Z) (p : point) : Prop :=
  exists pos, 0 <= pos < m /\ p = P0 (rd ord pos).

Lemma lower_correct : forall z i st k (H : Acc (Zwf 0) (gap n i)), gap n i = z ->
  1 <= (φ i) <= (φ n) -> 1 <= (φ k) <= (φ i) ->
  (φ (PArray.length st)) = 2 * (φ n) -> valid n st ->
  chain (fun j => P0 (rd st j)) 0 ((φ k) - 1) (PrL (φ i)) ->
  rd st 0 = rd ord 0 -> rd st ((φ k) - 1) = rd ord ((φ i) - 1) ->
  let r := lower x y ord st n k i H in
  1 <= (φ (snd r)) <= (φ n) /\ (φ (PArray.length (fst r))) = 2 * (φ n) /\ valid n (fst r) /\
  chain (fun j => P0 (rd (fst r) j)) 0 ((φ (snd r)) - 1) (PrL (φ n)) /\
  rd (fst r) 0 = rd ord 0 /\ rd (fst r) ((φ (snd r)) - 1) = rd ord ((φ n) - 1).
Proof.
  intro z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i st k H Hz Hi Hk Hl Hv Hc H0 Ht.
  destruct H as [H]. simpl.
  destruct (bdec (i <? n)%uint63) as [Hin | Hin].
  - pose proof Hin as Hin'. rewrite ltb_spec in Hin'.
    assert (Hi1 : (φ (i + 1)) = (φ i) + 1) by sia.
    set (q := ord.[i]).
    assert (Hqv : (φ q) < (φ n)) by apply Hord_valid.
    assert (Hq : forall p, PrL (φ i) p -> lex p (P0 q)).
    { intros p (pos & Hpos & Ep). subst p. unfold q. rewrite <- rd_phi.
      apply ord_mono; lia. }
    pose proof (pop_correct P0 HP0 st 1 q (PrL (φ i)) k Hv Hqv ltac:(change (φ 1) with 1; lia)
                  _ k (Zwf_well_founded 0 (φ k)) eq_refl ltac:(change (φ 1) with 1; lia)
                  ltac:(change (φ 1) with 1; apply popinv_init; [exact Hc | exact Hq]))
      as (Hk' & Hpi & Hstop).
    set (k' := pop x y st 1 k q (Zwf_well_founded 0 (φ k))) in *.
    change (φ 1) with 1 in Hk', Hpi, Hstop.
    assert (Hk1 : (φ (k' + 1)) = (φ k') + 1) by sia.
    assert (HkL : (φ k') < (φ (PArray.length st))) by lia.
    eapply IH; [ | reflexivity | lia | lia | | | | | ].
    + rewrite <- Hz. apply dec_step. exact Hin.
    + rewrite alength_set. exact Hl.
    + apply valid_set; [exact Hv | exact Hqv].
    + rewrite Hk1, Hi1. replace ((φ k') + 1 - 1) with ((φ k') - 1 + 1) by lia.
      apply (chain_push _ 0 ((φ k) - 1) ((φ k') - 1) (PrL (φ i)) (P0 q) Hpi).
      * destruct Hstop as [E | E]; [left; lia | right].
        replace ((φ k') - 1 - 1) with ((φ k') - 2) by lia. exact E.
      * exact Hq.
      * intros j Hj. simpl. rewrite rd_set_other by (rewrite ?wB_val; lia). reflexivity.
      * simpl. replace ((φ k') - 1 + 1) with (φ k') by lia. rewrite rd_set_same by exact HkL.
        reflexivity.
      * intros p (pos & Hpos & Ep). destruct (Z.eq_dec pos (φ i)) as [E | E].
        -- right. rewrite Ep, E. unfold q. rewrite rd_phi. reflexivity.
        -- left. exists pos. split; [lia | exact Ep].
      * exists (φ i). split; [lia|]. unfold q. rewrite rd_phi. reflexivity.
    + rewrite rd_set_other by (rewrite ?wB_val; lia). exact H0.
    + rewrite Hk1, Hi1. replace ((φ k') + 1 - 1) with (φ k') by lia.
      rewrite rd_set_same by exact HkL. replace ((φ i) + 1 - 1) with (φ i) by lia.
      unfold q. rewrite rd_phi. reflexivity.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hin.
    assert (Ein : (φ i) = (φ n)) by lia.
    simpl. rewrite Ein in Hc, Ht.
    split; [lia|]. split; [exact Hl|]. split; [exact Hv|]. split; [exact Hc|].
    split; assumption.
Qed.

Variable st1 : array int.
Variable L : int.

Definition PrU (m : Z) (p : point) : Prop :=
  exists pos, m <= pos < (φ n) /\ p = negp (P0 (rd ord pos)).

Lemma upper_correct : forall z j st k (H : Acc (Zwf 0) (φ j)), (φ j) = z ->
  (φ j) <= (φ n) - 1 -> 2 <= (φ L) <= (φ n) ->
  (φ L) <= (φ k) <= (φ L) + ((φ n) - 1 - (φ j)) -> ((φ j) < (φ n) - 1 -> (φ L) + 1 <= (φ k)) ->
  (φ (PArray.length st)) = 2 * (φ n) -> valid n st ->
  chain (fun m => negp (P0 (rd st m))) ((φ L) - 1) ((φ k) - 1) (PrU (φ j)) ->
  (forall m, 0 <= m < (φ L) -> rd st m = rd st1 m) ->
  rd st ((φ k) - 1) = rd ord (φ j) ->
  let r := upper x y ord st L k j H in
  (φ L) <= (φ (snd r)) <= (φ L) + ((φ n) - 1) /\ (0 < (φ n) - 1 -> (φ L) + 1 <= (φ (snd r))) /\
  (φ (PArray.length (fst r))) = 2 * (φ n) /\ valid n (fst r) /\
  chain (fun m => negp (P0 (rd (fst r) m))) ((φ L) - 1) ((φ (snd r)) - 1) (PrU 0) /\
  (forall m, 0 <= m < (φ L) -> rd (fst r) m = rd st1 m) /\
  rd (fst r) ((φ (snd r)) - 1) = rd ord 0.
Proof.
  intro z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j st k H Hz Hj HL Hk HkL1 Hl Hv Hc Hlow Ht.
  destruct H as [H]. simpl.
  destruct (bdec (0 <? j)%uint63) as [Hj0 | Hj0].
  - pose proof Hj0 as Hj0'. rewrite ltb_spec in Hj0'. change (φ 0) with 0 in Hj0'.
    assert (Hj1 : (φ (j - 1)) = (φ j) - 1) by sia.
    set (q := ord.[j - 1]).
    assert (Hqv : (φ q) < (φ n)) by apply Hord_valid.
    assert (Hq : forall p, PrU (φ j) p -> lex p (negp (P0 q))).
    { intros p (pos & Hpos & Ep). subst p. apply lex_neg. unfold q. rewrite <- rd_phi.
      rewrite Hj1. apply ord_mono; lia. }
    pose proof (pop_correct (fun i => negp (P0 i)) HP1 st L q (PrU (φ j)) k Hv Hqv ltac:(lia)
                  _ k (Zwf_well_founded 0 (φ k)) eq_refl ltac:(lia)
                  ltac:(apply popinv_init; [exact Hc | exact Hq]))
      as (Hk' & Hpi & Hstop).
    set (k' := pop x y st L k q (Zwf_well_founded 0 (φ k))) in *.
    assert (Hk1 : (φ (k' + 1)) = (φ k') + 1) by sia.
    assert (HkL : (φ k') < (φ (PArray.length st))) by lia.
    eapply IH; [ | reflexivity | lia | lia | lia | lia | | | | | ].
    + rewrite <- Hz. apply down_dec. exact Hj0.
    + rewrite alength_set. exact Hl.
    + apply valid_set; [exact Hv | exact Hqv].
    + rewrite Hk1, Hj1. replace ((φ k') + 1 - 1) with ((φ k') - 1 + 1) by lia.
      apply (chain_push _ ((φ L) - 1) ((φ k) - 1) ((φ k') - 1) (PrU (φ j)) (negp (P0 q)) Hpi).
      * destruct Hstop as [E | E]; [left; lia | right].
        replace ((φ k') - 1 - 1) with ((φ k') - 2) by lia. exact E.
      * exact Hq.
      * intros m Hm. simpl. rewrite rd_set_other by (rewrite ?wB_val; lia). reflexivity.
      * simpl. replace ((φ k') - 1 + 1) with (φ k') by lia. rewrite rd_set_same by exact HkL.
        reflexivity.
      * intros p (pos & Hpos & Ep). destruct (Z.eq_dec pos ((φ j) - 1)) as [E | E].
        -- right. rewrite Ep, E. unfold q. rewrite <- Hj1, rd_phi. reflexivity.
        -- left. exists pos. split; [lia | exact Ep].
      * exists ((φ j) - 1). split; [lia|]. unfold q. rewrite <- Hj1, rd_phi. reflexivity.
    + intros m Hm. rewrite rd_set_other by (rewrite ?wB_val; lia). apply Hlow. exact Hm.
    + rewrite Hk1, Hj1. replace ((φ k') + 1 - 1) with (φ k') by lia.
      rewrite rd_set_same by exact HkL.
      unfold q. rewrite <- Hj1, rd_phi. reflexivity.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hj0. change (φ 0) with 0 in Hj0.
    assert (Ej : (φ j) = 0) by (pose proof (to_Z_bounded j); lia).
    simpl. rewrite Ej in Hc, Ht, Hk, HkL1.
    split; [lia|]. split; [intro; apply HkL1; lia|].
    split; [exact Hl|]. split; [exact Hv|]. split; [exact Hc|].
    split; assumption.
Qed.

End Scan.

(* ------------------------------------------------------------------ *)
(* From the polygon to the contract                                    *)
(* ------------------------------------------------------------------ *)

Section Final.
Local Open Scope Z_scope.

Lemma copy_correct : forall (src : array int) (h : int), (φ h) <= 4194303 ->
  forall z i dst (H : Acc (Zwf 0) (gap h i)), gap h i = z ->
  (φ i) <= (φ h) -> (φ (PArray.length dst)) = (φ h) ->
  (forall m, 0 <= m < (φ i) -> rd dst m = rd src m) ->
  let r := copyl src dst h i H in
  (φ (PArray.length r)) = (φ h) /\ (forall m, 0 <= m < (φ h) -> rd r m = rd src m).
Proof.
  intros src h Hh z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i dst H Hz Hi Hl Hc.
  destruct H as [H]. simpl.
  destruct (bdec (i <? h)%uint63) as [Hc' | Hc'].
  - pose proof Hc' as Hc''. rewrite ltb_spec in Hc''.
    assert (Hi1 : (φ (i + 1)) = (φ i) + 1) by sia.
    eapply IH; [ | reflexivity | | | ].
    + rewrite <- Hz. apply dec_step. exact Hc'.
    + lia.
    + rewrite alength_set. exact Hl.
    + intros m Hm. rewrite Hi1 in Hm. destruct (Z.eq_dec m (φ i)) as [E | E].
      * subst m. rewrite rd_set_same by lia. symmetry. apply rd_phi.
      * rewrite rd_set_other by (rewrite ?wB_val; lia). apply Hc. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hc'.
    split; [exact Hl|]. intros m Hm. apply Hc. lia.
Qed.

Lemma chain_ext : forall c c' b t Pr, chain c b t Pr ->
  (forall j, b <= j <= t -> c' j = c j) -> chain c' b t Pr.
Proof.
  intros c c' b t Pr Hc He. destruct Hc as [H1 H2 H3 H4 H5 H6 H7].
  constructor.
  - exact H1.
  - intros j Hj. rewrite !He by lia. apply H2. exact Hj.
  - intros j Hj1 Hj2. rewrite !He by lia. apply H3; assumption.
  - intros j p Hj Hp. rewrite !He by lia. apply H4; assumption.
  - intros p Hp. rewrite He by lia. apply H5. exact Hp.
  - intros p Hp. rewrite He by lia. apply H6. exact Hp.
  - rewrite He by lia. exact H7.
Qed.

Lemma chain_single : forall (c : Z -> point) b (Pr : point -> Prop),
  (forall p, Pr p -> p = c b) -> Pr (c b) -> chain c b b Pr.
Proof.
  intros c b Pr H1 H2. constructor.
  - lia.
  - intros j Hj. lia.
  - intros j Hj1 Hj2. lia.
  - intros j p Hj. lia.
  - intros p Hp. rewrite (H1 p Hp). apply lex_refl.
  - intros p Hp. rewrite (H1 p Hp). apply lex_refl.
  - exact H2.
Qed.

Lemma get_pt_map : forall (e : Z -> point) (h : nat) (t : N), (t < N.of_nat h)%N ->
  get_pt (map (fun m => e (Z.of_nat m)) (seq 0 h)) t = e (Z.of_N t).
Proof.
  intros e h t Ht. unfold get_pt.
  rewrite nth_indep with (d' := e (Z.of_nat 0))
    by (rewrite length_map, length_seq; lia).
  change (e (Z.of_nat 0)) with ((fun m => e (Z.of_nat m)) 0%nat).
  rewrite map_nth, seq_nth by lia. cbv beta. f_equal. lia.
Qed.

Lemma len_map_seq : forall (e : Z -> point) (h : nat),
  len (map (fun m => e (Z.of_nat m)) (seq 0 h)) = N.of_nat h.
Proof. intros. unfold len. rewrite length_map, length_seq. reflexivity. Qed.

Lemma next_map_seq : forall (e : Z -> point) (h : nat) (t : N), (t < N.of_nat h)%N ->
  next (map (fun m => e (Z.of_nat m)) (seq 0 h)) t
  = if (t + 1 <? N.of_nat h)%N then (t + 1)%N else 0%N.
Proof.
  intros e h t Ht. unfold next. rewrite len_map_seq.
  destruct (N.ltb_spec (t + 1) (N.of_nat h)).
  - apply N.mod_small. exact H.
  - replace (t + 1)%N with (N.of_nat h) by lia. apply N.mod_same. lia.
Qed.

Lemma final_spec : forall xs ys (e : Z -> point) (h : nat) (S : point -> Prop) (hl : list N),
  (2 <= h)%nat ->
  vertices xs ys hl = map (fun m => e (Z.of_nat m)) (seq 0 h) ->
  List.length hl = h -> indices_valid xs hl ->
  (forall i, (i < len xs)%N -> S (get_point xs ys i)) ->
  e (Z.of_nat h) = e 0 ->
  (forall i j, 0 <= i < j -> j <= Z.of_nat h - 1 -> e i <> e j) ->
  (forall j p, 0 <= j < Z.of_nat h -> S p -> 0 <= cross (e j) (e (j + 1)) p) ->
  ((3 <= h)%nat -> forall j, 0 <= j <= Z.of_nat h - 2 -> 0 < cross (e j) (e (j + 1)) (e (j + 2))) ->
  ((3 <= h)%nat -> 0 < cross (e (Z.of_nat h - 1)) (e 0) (e 1)) ->
  (h = 2%nat -> forall p, S p -> on_segment (e 0) (e 1) p) ->
  convex_hull_spec xs ys hl.
Proof.
  intros xs ys e h S hl Hh Hvert Hlen Hidx HS Hend Hnd Hleft Hcvx Hwrap Hseg.
  unfold convex_hull_spec. cbv zeta. rewrite Hvert.
  split; [unfold len; rewrite Hlen; lia|].
  clear Hlen.
  split; [exact Hidx|].
  split.
  { apply NoDup_map_NoDup_ForallPairs; [|apply seq_NoDup].
    intros a b Ha Hb E. apply in_seq in Ha, Hb.
    destruct (Nat.lt_trichotomy a b) as [L | [L | L]]; [| exact L |].
    - exfalso. apply (Hnd (Z.of_nat a) (Z.of_nat b)); [lia | lia | exact E].
    - exfalso. apply (Hnd (Z.of_nat b) (Z.of_nat a)); [lia | lia | symmetry; exact E]. }
  split.
  { intros H3 t Ht. rewrite len_map_seq in H3, Ht.
    assert (H3' : (3 <= h)%nat) by lia.
    rewrite (next_map_seq e h t Ht).
    destruct (N.ltb_spec (t + 1) (N.of_nat h)) as [T1 | T1].
    - rewrite (next_map_seq e h (t + 1) T1).
      destruct (N.ltb_spec (t + 1 + 1) (N.of_nat h)) as [T2 | T2].
      + rewrite !get_pt_map by lia.
        replace (Z.of_N (t + 1)) with (Z.of_N t + 1) by lia.
        replace (Z.of_N (t + 1 + 1)) with (Z.of_N t + 2) by lia.
        apply Hcvx; [exact H3' | lia].
      + rewrite !get_pt_map by lia.
        replace (Z.of_N (t + 1)) with (Z.of_N t + 1) by lia.
        change (Z.of_N 0) with 0. rewrite <- Hend.
        replace (Z.of_nat h) with (Z.of_N t + 2) by lia.
        apply Hcvx; [exact H3' | lia].
    - rewrite (next_map_seq e h 0 ltac:(lia)).
      destruct (N.ltb_spec (0 + 1) (N.of_nat h)) as [T2 | T2]; [|lia].
      rewrite !get_pt_map by lia. change (Z.of_N 0) with 0. change (Z.of_N (0 + 1)) with 1.
      replace (Z.of_N t) with (Z.of_nat h - 1) by lia. apply Hwrap. exact H3'. }
  assert (Hlo : left_of_edges xs ys (map (fun m => e (Z.of_nat m)) (seq 0 h))).
  { intros t i Ht Hi. rewrite len_map_seq in Ht.
    rewrite (next_map_seq e h t Ht).
    destruct (N.ltb_spec (t + 1) (N.of_nat h)) as [T1 | T1].
    - rewrite !get_pt_map by lia.
      replace (Z.of_N (t + 1)) with (Z.of_N t + 1) by lia.
      apply Hleft; [lia | apply HS; exact Hi].
    - rewrite !get_pt_map by lia. change (Z.of_N 0) with 0. rewrite <- Hend.
      replace (Z.of_nat h) with (Z.of_N t + 1) by lia.
      apply Hleft; [lia | apply HS; exact Hi]. }
  destruct (Nat.eq_dec h 2) as [E2 | E2].
  - subst h. simpl. intros i Hi. apply (Hseg eq_refl). apply HS. exact Hi.
  - destruct h as [| [| [| h']]]; [lia | lia | lia |].
    unfold encloses. simpl. simpl in Hlo. exact Hlo.
Qed.

End Final.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Lemma repr_len_s : forall (x : array sint) (a : list Z), repr x a ->
  (φ (PArray.length x)) = Z.of_nat (List.length a).
Proof. intros x a [Hl _]. symmetry. exact Hl. Qed.

Lemma repr_cell : forall (x : array int) (a : list Z), @repr (array sint) (list Z) _ x a ->
  forall i : int, ((φ i) < Z.of_nat (List.length a))%Z ->
  Sint63.to_Z x.[i] = get_list_Z a (Z.to_N (φ i)).
Proof.
  intros x a [Hl Hc] i Hi.
  destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (m & Hm & Hr).
  unfold repr, repr_sint in Hr.
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded i); lia).
  rewrite of_to_Z in Hr.
  transitivity m; [exact Hr|].
  unfold get_list_Z. rewrite Z_N_nat. symmetry. apply nth_error_nth. exact Hm.
Qed.

Lemma repr_out : forall (r : array int) (g : Z -> N) (h : nat),
  (φ (PArray.length r)) = Z.of_nat h ->
  (forall m, (0 <= m < Z.of_nat h)%Z -> Z.to_N (φ (rd r m)) = g m) ->
  repr (r : array uint) (map (fun m => g (Z.of_nat m)) (seq 0 h)).
Proof.
  intros r g h Hl Hg. split.
  - rewrite length_map, length_seq. symmetry. exact Hl.
  - intros kk Hk. rewrite length_map, length_seq in Hk.
    exists (g (Z.of_nat kk)). split.
    + rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec kk h); [reflexivity | lia].
    + unfold repr, repr_uint. exact (Hg (Z.of_nat kk) ltac:(lia)).
Qed.

Lemma deg_iff : forall (x y : array int) (a b : int),
  ((x.[a] =? x.[b]) && (y.[a] =? y.[b]))%uint63 = true <-> Pt x y a = Pt x y b.
Proof.
  intros x y a b. rewrite Bool.andb_true_iff, !eqb_spec. unfold Pt. split.
  - intros [E1 E2]. rewrite E1, E2. reflexivity.
  - intros E. pose proof (f_equal fst E) as E1. pose proof (f_equal snd E) as E2.
    cbn [fst snd] in E1, E2. split; apply Sint63.to_Z_inj; assumption.
Qed.

Lemma hull_correct : forall (xs ys : list Z) (x y : array sint),
  valid_input xs ys -> repr x xs -> repr y ys ->
  exists h : list N, repr (hull x y) h /\ convex_hull_spec xs ys h.
Proof.
  intros xs ys x y Hv Hx Hy.
  unfold hull. cbv zeta.
  lazymatch goal with |- context [msort x y ?N] => set (n := N) end.
  destruct Hv as [Hn Hly Hbx Hby]. unfold len in Hn, Hly.
  assert (Lx : (φ n) = Z.of_nat (List.length xs)) by exact (repr_len_s x xs Hx).
  pose proof (repr_len_s y ys Hy) as Ly.
  assert (Lyx : List.length ys = List.length xs) by lia.
  assert (Hn' : (1 <= (φ n) <= 10000)%Z) by lia.
  assert (Hpt : forall a : int, ((φ a) < (φ n))%Z -> Pt x y a = get_point xs ys (Z.to_N (φ a))).
  { intros a Ha. unfold Pt, get_point.
    f_equal; [apply (repr_cell x xs Hx) | apply (repr_cell y ys Hy)]; lia. }
  assert (Hcoord : forall a : int, ((φ a) < (φ n))%Z ->
    (-10000 <= Sint63.to_Z x.[a] <= 10000 /\ -10000 <= Sint63.to_Z y.[a] <= 10000)%Z).
  { intros a Ha. pose proof (Hpt a Ha) as E. unfold get_point in E.
    assert (E1 : fst (Pt x y a) = get_list_Z xs (Z.to_N (φ a))) by (rewrite E; reflexivity).
    assert (E2 : snd (Pt x y a) = get_list_Z ys (Z.to_N (φ a))) by (rewrite E; reflexivity).
    rewrite Forall_nth in Hbx, Hby. split.
    - change (Sint63.to_Z x.[a]) with (fst (Pt x y a)). rewrite E1.
      unfold get_list_Z. apply Hbx. lia.
    - change (Sint63.to_Z y.[a]) with (snd (Pt x y a)). rewrite E2.
      unfold get_list_Z. apply Hby. lia. }
  assert (Hgp : forall i : N, (i < len xs)%N ->
            get_point xs ys i = Pt x y (of_Z (Z.of_N i))).
  { intros i Hi. unfold len in Hi.
    rewrite Hpt by (rewrite phi_of_Z by (rewrite wB_val; lia); lia).
    rewrite phi_of_Z by (rewrite wB_val; lia). f_equal. lia. }
  destruct (msort_correct x y n Hn') as (Hol & Hos & Hoc & Hov).
  set (ord := msort x y n) in *.
  assert (Hmono : forall p1 p2, (0 <= p1 <= p2)%Z -> (p2 < (φ n))%Z ->
            lex (Pt x y (rd ord p1)) (Pt x y (rd ord p2)))
    by (apply ord_mono; exact Hos).
  assert (HSin : forall i : N, (i < len xs)%N ->
            exists pos, (0 <= pos < (φ n))%Z /\ get_point xs ys i = Pt x y (rd ord pos)).
  { intros i Hi. rewrite Hgp by exact Hi. unfold len in Hi.
    destruct (Hoc (of_Z (Z.of_N i)) ltac:(rewrite phi_of_Z by (rewrite wB_val; lia); lia))
      as (pos & Hpos & Ep).
    exists pos. split; [exact Hpos | rewrite Ep; reflexivity]. }
  set (a := ord.[0]). set (b := ord.[n - 1]).
  assert (Ha : rd ord 0 = a) by reflexivity.
  assert (Hb : rd ord ((φ n) - 1) = b) by (unfold b; rewrite <- rd_phi; f_equal; sia).
  assert (Hav : ((φ a) < (φ n))%Z) by apply Hov.
  clearbody ord a b.
  destruct ((x.[a] =? x.[b]) && (y.[a] =? y.[b]))%uint63 eqn:Edeg.
  - (* all the points coincide *)
    apply deg_iff in Edeg.
    exists [Z.to_N (φ a)]. split.
    + change [Z.to_N (φ a)] with
        (map (fun m => (fun _ : Z => Z.to_N (φ a)) (Z.of_nat m)) (seq 0 1)).
      apply repr_out.
      * rewrite alength_make_small by lia. reflexivity.
      * intros m Hm. rewrite rd_make. reflexivity.
    + unfold convex_hull_spec. cbv zeta. unfold vertices. simpl map.
      split; [unfold len; simpl; lia|].
      split; [constructor; [unfold len; lia | constructor]|].
      split; [constructor; [intros [] | constructor]|].
      split; [unfold len; simpl; lia|].
      unfold encloses. intros i Hi.
      destruct (HSin i Hi) as (pos & Hpos & Ep). rewrite Ep. rewrite <- Hpt by exact Hav.
      apply lex_antisym.
      * rewrite Edeg, <- Hb. apply Hmono; lia.
      * rewrite <- Ha. apply Hmono; lia.
  - (* the general case *)
    assert (HAB : Pt x y a <> Pt x y b)
      by (intro E; apply deg_iff in E;
          assert (F : true = false) by (rewrite <- Edeg; symmetry; exact E);
          discriminate F).
    assert (Hn2 : (2 <= (φ n))%Z).
    { destruct (Z.eq_dec (φ n) 1) as [E | E]; [|lia]. exfalso. apply HAB.
      rewrite <- Ha, <- Hb, E. reflexivity. }
    lazymatch goal with |- context [lower x y ord ?S n 1 1 _] => set (st0 := S) end.
    assert (Hst0l : (φ (PArray.length st0)) = (2 * (φ n))%Z).
    { unfold st0. rewrite alength_set, alength_make_small by sia. sia. }
    assert (Hst0v : valid n st0) by (apply valid_set; [exact (valid_make n Hn' _) | exact Hav]).
    assert (Hst00 : rd st0 0 = a).
    { change 0%Z with (φ 0). unfold st0. apply rd_set_same.
      rewrite alength_make_small by sia. change (φ 0) with 0%Z. sia. }
    clearbody st0.
    assert (Hc0 : chain (fun j => Pt x y (rd st0 j)) 0 ((φ 1) - 1) (PrL x y ord (φ 1))).
    { change (φ 1) with 1%Z. replace (1 - 1)%Z with 0%Z by lia. apply chain_single.
      - intros p (pos & Hpos & Ep). replace pos with 0%Z in Ep by lia.
        rewrite Ep, Ha, Hst00. reflexivity.
      - exists 0%Z. split; [lia|]. rewrite Hst00, Ha. reflexivity. }
    assert (Hst00' : rd st0 0 = rd ord 0) by (rewrite Hst00, Ha; reflexivity).
    assert (Hst01 : rd st0 ((φ 1) - 1) = rd ord ((φ 1) - 1)) by exact Hst00'.
    pose proof (lower_correct x y n Hn' Hcoord ord Hol Hos Hov _ 1 st0 1
                 (Zwf_well_founded 0 (gap n 1)) eq_refl
                 ltac:(change (φ 1) with 1%Z; lia) ltac:(change (φ 1) with 1%Z; lia)
                 Hst0l Hst0v Hc0 Hst00' Hst01) as Hlow0.
    cbv zeta in Hlow0.
    lazymatch goal with |- context [lower x y ord st0 n 1 1 ?H] =>
      destruct (lower x y ord st0 n 1 1 H) as [st1 l] eqn:El end.
    try rewrite El in Hlow0. cbn [fst snd] in Hlow0.
    destruct Hlow0 as (Hl1 & Hst1l & Hst1v & Hch1 & Hst10 & Hst1t).
    assert (HL2 : (2 <= (φ l))%Z).
    { destruct (Z.eq_dec (φ l) 1) as [E | E]; [|lia]. exfalso. apply HAB.
      rewrite E in Hst1t. replace (1 - 1)%Z with 0%Z in Hst1t by lia.
      rewrite <- Ha, <- Hb, <- Hst10, <- Hst1t. reflexivity. }
    assert (Hn1 : (φ (n - 1)) = ((φ n) - 1)%Z) by sia.
    assert (Hc1 : chain (fun m => negp (Pt x y (rd st1 m))) ((φ l) - 1) ((φ l) - 1)
                    (PrU x y n ord (φ (n - 1)))).
    { rewrite Hn1. apply chain_single.
      - intros p (pos & Hpos & Ep). replace pos with ((φ n) - 1)%Z in Ep by lia.
        rewrite Ep, Hst1t. reflexivity.
      - exists ((φ n) - 1)%Z. split; [lia|]. rewrite Hst1t. reflexivity. }
    pose proof (upper_correct x y n Hn' Hcoord ord Hos Hov st1 l _ (n - 1) st1 l
                 (Zwf_well_founded 0 (φ (n - 1))) eq_refl ltac:(lia) ltac:(lia) ltac:(lia)
                 ltac:(lia) Hst1l Hst1v Hc1 ltac:(intros; reflexivity)
                 ltac:(rewrite Hn1; exact Hst1t)) as Hup0.
    cbv zeta in Hup0.
    lazymatch goal with |- context [upper x y ord st1 l l (n - 1) ?H] =>
      destruct (upper x y ord st1 l l (n - 1) H) as [st2 k] eqn:Eu end.
    try rewrite Eu in Hup0. cbn [fst snd] in Hup0.
    destruct Hup0 as (Hk1 & Hk2 & Hst2l & Hst2v & Hch2 & Hlowc & Hst2t).
    specialize (Hk2 ltac:(lia)).
    assert (Hkm1 : (φ (k - 1)) = ((φ k) - 1)%Z) by sia.
    lazymatch goal with |- context [copyl st2 ?D (k - 1) 0 ?H] =>
      set (D0 := D); set (H0 := H) end.
    destruct (copy_correct st2 (k - 1) ltac:(lia) _ 0 D0 H0 eq_refl
                ltac:(change (φ 0) with 0%Z; lia)
                ltac:(unfold D0; rewrite alength_make_small by lia; reflexivity)
                ltac:(intros m Hm; change (φ 0) with 0%Z in Hm; lia))
      as (Hrl & Hrc).
    set (e := fun m => Pt x y (rd st2 m)).
    set (h := Z.to_nat ((φ k) - 1)).
    set (S := PrL x y ord (φ n)).
    set (SN := PrU x y n ord 0).
    assert (PHlow : chain e 0 ((φ l) - 1) S).
    { apply (chain_ext _ _ _ _ _ Hch1). intros j Hj. unfold e. rewrite Hlowc by lia.
      reflexivity. }
    assert (PHup : chain (fun j => negp (e j)) ((φ l) - 1) ((φ k) - 1) SN) by exact Hch2.
    assert (PHSN : forall p, S p -> SN (negp p)).
    { intros p (pos & Hpos & Ep). exists pos. split; [lia | rewrite Ep; reflexivity]. }
    assert (PHend : e ((φ k) - 1)%Z = e 0%Z).
    { unfold e. rewrite Hst2t, Hlowc by lia. rewrite Hst10. reflexivity. }
    assert (PHAB : e 0%Z <> e ((φ l) - 1)%Z).
    { unfold e. rewrite !Hlowc by lia. rewrite Hst10, Hst1t, Ha, Hb. exact HAB. }
    assert (PHS : forall j, (0 <= j < (φ k))%Z -> S (e j)).
    { intros j Hj. destruct (Hoc (rd st2 j) (valid_rd n st2 j Hst2v)) as (pos & Hpos & Ep).
      exists pos. split; [exact Hpos | unfold e; rewrite Ep; reflexivity]. }
    assert (HK : ((φ l) + 1 <= (φ k))%Z) by lia.
    exists (map (fun m => (fun z => Z.to_N (φ (rd st2 z))) (Z.of_nat m)) (seq 0 h)).
    split.
    + assert (HA : (φ (PArray.length (copyl st2 D0 (k - 1) 0 H0))) = Z.of_nat h)
        by (etransitivity; [exact Hrl | unfold h; lia]).
      assert (HB : forall m, (0 <= m < Z.of_nat h)%Z ->
                Z.to_N (φ (rd (copyl st2 D0 (k - 1) 0 H0) m)) = Z.to_N (φ (rd st2 m))).
      { intros m Hm. rewrite Hrc by (unfold h in Hm; lia). reflexivity. }
      exact (repr_out _ (fun z => Z.to_N (φ (rd st2 z))) h HA HB).
    + apply final_spec with (e := e) (h := h) (S := S).
      * unfold h. lia.
      * unfold vertices. rewrite map_map. apply map_ext_in. intros m Hm.
        unfold e. symmetry. apply Hpt. apply valid_rd. exact Hst2v.
      * rewrite length_map, length_seq. reflexivity.
      * apply Forall_forall. intros i Hi. apply in_map_iff in Hi.
        destruct Hi as (m & Em & Hm). subst i. unfold len.
        pose proof (valid_rd n st2 (Z.of_nat m) Hst2v). lia.
      * intros i Hi. destruct (HSin i Hi) as (pos & Hpos & Ep).
        exists pos. split; [lia | exact Ep].
      * replace (Z.of_nat h) with ((φ k) - 1)%Z by (unfold h; lia). exact PHend.
      * intros i j Hij Hj.
        apply (poly_nodup e (φ l) (φ k) S SN HL2 HK PHlow PHup PHSN PHend PHAB PHS);
          unfold h in Hj; lia.
      * intros j p Hj Hp.
        apply (all_left e (φ l) (φ k) S SN PHlow PHup PHSN); [unfold h in Hj; lia | exact Hp].
      * intros H3 j Hj.
        apply (cvx_full e (φ l) (φ k) S SN HL2 HK PHlow PHup PHSN PHend PHAB PHS);
          unfold h in H3, Hj; lia.
      * intros H3. replace (Z.of_nat h - 1)%Z with ((φ k) - 2)%Z by (unfold h; lia).
        apply (junction2 e (φ l) (φ k) S SN HL2 HK PHlow PHup PHSN PHend PHAB PHS).
        unfold h in H3. lia.
      * intros H2 p Hp.
        apply (poly_seg e (φ l) (φ k) S SN HL2 HK PHlow PHup PHSN PHend);
          [unfold h in H2; lia | exact Hp].
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition convex_hull : array sint -> array sint -> array uint := hull.
Elpi complexity convex_hull.

Definition convex_hull_correct : forall (xs ys : list Z) (x y : array sint),
  valid_input xs ys -> repr x xs -> repr y ys ->
  exists h : list N, repr (convex_hull x y) h /\ convex_hull_spec xs ys h
  := hull_correct.

(* ------------------------------------------------------------------ *)
(* Cost                                                                *)
(* ------------------------------------------------------------------ *)

(* The cost translation: [Elpi complexity] on sumbool, bdec, andb and every
   function of the program, callee first (min_i, cross_m, le_pt, take_left,
   merge, pass, sortl, initl, msort, pop, lower, upper, copyl, hull), then
   convex_hull.  Each loop is bounded on its twin by induction on a nat bound
   of its measure (the Acc proof destructed so that cost_simpl unfolds the fix
   once), the callees' bounds generalized in their callers' goals:
     merge  <= gap hi k * 200 + 10           pass  <= gap n lo * 400 + 50
     sortl  <= m * (n * 400 + 100) + 50      when n <= 2^m * w (w doubles)
     initl, copyl <= gap * 50 + 20
     pop    : cost + k' * 150 <= k * 150 + 150          (k' its result)
     lower  <= gap n i * 400 + k * 150 + 50 (potential: the stack height k)
     upper  <= j * 400 + k * 150 + 50
     msort  <= (log2 n + 1) * (n * 400 + 100) + n * 50 + 200
     hull   <= (log2 n + 1) * (n * 400 + 100) + n * 2000 + 1000 (valid input)
   so convex_hull_time holds with c1 = 3000, c2 = 1000.  The pops are paid by
   the drop of the stack height: one step of a scan costs a constant plus
   150 per popped cell, and pushes one cell (150 of potential).  hull needs
   the premises: the copy loop runs k - 1 times, k the final stack height,
   which the correctness lemmas bound by 1 <= k <= 2n on a valid input
   (hull_facts; on k = 0 the word k - 1 would wrap).  The Arguments ... :
   simpl never below (gap, mz, zn, cross_m, andb_cost and Uint63.to_Z) keep
   cbn away from the measures, which sit in the Acc indices. *)

(* The two scans' stack heights, from the correctness lemmas: on a valid
   input with distinct extreme points, 2 <= l <= n and l + 1 <= k <= l + n - 1. *)
Lemma hull_facts : forall (xs ys : list Z) (x y : array sint),
  valid_input xs ys -> repr x xs -> repr y ys ->
  let n := PArray.length x in
  let ord := msort x y n in
  ((x.[ord.[0]] =? x.[ord.[(n - 1)%uint63]]) && (y.[ord.[0]] =? y.[ord.[(n - 1)%uint63]]))%uint63 = false ->
  forall st1 l, lower x y ord (PArray.make (n + n) 0).[0 <- ord.[0]] n 1 1
                  (Zwf_well_founded 0 (gap n 1)) = (st1, l) ->
  (φ l <= φ n)%Z /\
  forall st2 k, upper x y ord st1 l l (n - 1) (Zwf_well_founded 0 (φ (n - 1)%uint63)) = (st2, k) ->
  (1 <= φ k <= 2 * φ n)%Z.
Proof.
  intros xs ys x y Hv Hx Hy n ord Edeg st1 l El.
  destruct Hv as [Hn Hly Hbx Hby]. unfold len in Hn, Hly.
  assert (Lx : (φ n) = Z.of_nat (List.length xs)) by exact (repr_len_s x xs Hx).
  assert (Hn' : (1 <= (φ n) <= 10000)%Z) by lia.
  assert (Hpt : forall a : int, ((φ a) < (φ n))%Z -> Pt x y a = get_point xs ys (Z.to_N (φ a))).
  { intros a Ha. unfold Pt, get_point.
    f_equal; [apply (repr_cell x xs Hx) | apply (repr_cell y ys Hy)]; lia. }
  assert (Hcoord : forall a : int, ((φ a) < (φ n))%Z ->
    (-10000 <= Sint63.to_Z x.[a] <= 10000 /\ -10000 <= Sint63.to_Z y.[a] <= 10000)%Z).
  { intros a Ha. pose proof (Hpt a Ha) as E. unfold get_point in E.
    assert (E1 : fst (Pt x y a) = get_list_Z xs (Z.to_N (φ a))) by (rewrite E; reflexivity).
    assert (E2 : snd (Pt x y a) = get_list_Z ys (Z.to_N (φ a))) by (rewrite E; reflexivity).
    rewrite Forall_nth in Hbx, Hby. split.
    - change (Sint63.to_Z x.[a]) with (fst (Pt x y a)). rewrite E1.
      unfold get_list_Z. apply Hbx. lia.
    - change (Sint63.to_Z y.[a]) with (snd (Pt x y a)). rewrite E2.
      unfold get_list_Z. apply Hby. lia. }
  destruct (msort_correct x y n Hn') as (Hol & Hos & Hoc & Hov).
  fold ord in Hol, Hos, Hoc, Hov.
  set (a := ord.[0]) in *. set (b := ord.[(n - 1)%uint63]) in *.
  assert (Ha : rd ord 0 = a) by reflexivity.
  assert (Hb : rd ord ((φ n) - 1) = b) by (unfold b; rewrite <- rd_phi; f_equal; sia).
  assert (Hav : ((φ a) < (φ n))%Z) by apply Hov.
  clearbody ord a b.
  assert (HAB : Pt x y a <> Pt x y b)
    by (intro E; apply deg_iff in E;
        assert (F : true = false) by (rewrite <- Edeg; symmetry; exact E);
        discriminate F).
  assert (Hn2 : (2 <= (φ n))%Z).
  { destruct (Z.eq_dec (φ n) 1) as [E | E]; [|lia]. exfalso. apply HAB.
    rewrite <- Ha, <- Hb, E. reflexivity. }
  revert El.
  lazymatch goal with |- lower x y ord ?S n 1 1 _ = _ -> _ => set (st0 := S) end.
  intros El.
  assert (Hst0l : (φ (PArray.length st0)) = (2 * (φ n))%Z).
  { unfold st0. rewrite alength_set, alength_make_small; sia. }
  assert (Hst0v : valid n st0) by (apply valid_set; [exact (valid_make n Hn' _) | exact Hav]).
  assert (Hst00 : rd st0 0 = a).
  { change 0%Z with (φ 0). unfold st0. apply rd_set_same.
    rewrite alength_make_small; [sia|]. change (φ 0) with 0%Z. sia. }
  clearbody st0.
  assert (Hc0 : chain (fun j => Pt x y (rd st0 j)) 0 ((φ 1) - 1) (PrL x y ord (φ 1))).
  { change (φ 1) with 1%Z. replace (1 - 1)%Z with 0%Z by lia. apply chain_single.
    - intros p (pos & Hpos & Ep). replace pos with 0%Z in Ep by lia.
      rewrite Ep, Ha, Hst00. reflexivity.
    - exists 0%Z. split; [lia|]. rewrite Hst00, Ha. reflexivity. }
  assert (Hst00' : rd st0 0 = rd ord 0) by (rewrite Hst00, Ha; reflexivity).
  assert (Hst01 : rd st0 ((φ 1) - 1) = rd ord ((φ 1) - 1)) by exact Hst00'.
  pose proof (lower_correct x y n Hn' Hcoord ord Hol Hos Hov _ 1 st0 1
               (Zwf_well_founded 0 (gap n 1)) eq_refl
               ltac:(change (φ 1) with 1%Z; lia) ltac:(change (φ 1) with 1%Z; lia)
               Hst0l Hst0v Hc0 Hst00' Hst01) as Hlow0.
  cbv zeta in Hlow0. rewrite El in Hlow0. cbn [fst snd] in Hlow0.
  destruct Hlow0 as (Hl1 & Hst1l & Hst1v & Hch1 & Hst10 & Hst1t).
  split; [lia|].
  intros st2 k Eu.
  assert (HL2 : (2 <= (φ l))%Z).
  { destruct (Z.eq_dec (φ l) 1) as [E | E]; [|lia]. exfalso. apply HAB.
    rewrite E in Hst1t. replace (1 - 1)%Z with 0%Z in Hst1t by lia.
    rewrite <- Ha, <- Hb, <- Hst10, <- Hst1t. reflexivity. }
  assert (Hn1 : (φ (n - 1)%uint63) = ((φ n) - 1)%Z) by sia.
  assert (Hc1 : chain (fun m => negp (Pt x y (rd st1 m))) ((φ l) - 1) ((φ l) - 1)
                  (PrU x y n ord (φ (n - 1)%uint63))).
  { rewrite Hn1. apply chain_single.
    - intros p (pos & Hpos & Ep). replace pos with ((φ n) - 1)%Z in Ep by lia.
      rewrite Ep, Hst1t. reflexivity.
    - exists ((φ n) - 1)%Z. split; [lia|]. rewrite Hst1t. reflexivity. }
  pose proof (upper_correct x y n Hn' Hcoord ord Hos Hov st1 l _ (n - 1) st1 l
               (Zwf_well_founded 0 (φ (n - 1)%uint63)) eq_refl ltac:(lia) ltac:(lia) ltac:(lia)
               ltac:(lia) Hst1l Hst1v Hc1 ltac:(intros; reflexivity)
               ltac:(rewrite Hn1; exact Hst1t)) as Hup0.
  cbv zeta in Hup0. rewrite Eu in Hup0. cbn [fst snd] in Hup0.
  destruct Hup0 as (Hk1 & Hk2 & _). lia.
Qed.


Lemma bdec_time b (w : bool_cost stepsCM b) : (cost (bdec_cost stepsCM b w) <= 2)%nat.
Proof. destruct w; cbn; lia. Qed.

Lemma andb_time a aC b bC : (cost (extract (andb_cost stepsCM a aC) b bC) <= 2)%nat.
Proof. destruct aC; cbn; lia. Qed.

Lemma min_i_time a aC b bC : (cost (extract (min_i_cost stepsCM a aC) b bC) <= 10)%nat.
Proof. unfold min_i_cost. cost_simpl. cost_destruct (a <? b); cost_simpl; lia. Qed.

Lemma cross_m_time x xC y yC a aC b bC c cC :
  (cost (extract (extract (extract (extract (cross_m_cost stepsCM x xC) y yC) a aC) b bC) c cC) <= 50)%nat.
Proof. unfold cross_m_cost. cost_simpl. lia. Qed.

Lemma le_pt_time x xC y yC a aC b bC :
  (cost (extract (extract (extract (le_pt_cost stepsCM x xC) y yC) a aC) b bC) <= 30)%nat.
Proof.
  unfold le_pt_cost. cost_simpl.
  destruct (ltsb x.[a] x.[b]); cost_simpl; [lia|].
  destruct (x.[a] =? x.[b]); cost_simpl; lia.
Qed.

Ltac zero_partials :=
  repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch T with forall _, _ => change (@cost T X) with 0%nat end end.
Ltac zero_pairs := repeat match goal with |- context [@cost ?T (?z, ?x)] => change (@cost T (z, x)) with 0%nat end.
Ltac set_simpl :=
  repeat match goal with
  | |- context [cost (extract (extract (extract (set_cost ?a ?b ?c) ?d ?e) ?f ?g) ?h ?i)] =>
      change (cost (extract (extract (extract (set_cost a b c) d e) f g) h i)) with 1%nat
  end.

Lemma take_left_time x xC y yC src srcC mid midC hi hiC i iC j jC :
  (cost (extract (extract (extract (extract (extract (extract (take_left_cost stepsCM x xC) y yC) src srcC) mid midC) hi hiC) i iC) j jC) <= 60)%nat.
Proof.
  unfold take_left_cost. cost_simpl.
  cost_destruct (i <? mid); cost_simpl; [|lia].
  cost_destruct (j <? hi); cost_simpl; [|lia].
  zero_partials.
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with extract (extract (extract (le_pt_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC =>
    pose proof (le_pt_time a aC b bC c cC d dC : (@cost T X <= _)%nat) end end.
  lia.
Qed.

Arguments gap : simpl never.
Arguments mz : simpl never.

Lemma gap_S (i n : int) : (i <? n) = true -> Z.to_nat (gap n i) = S (Z.to_nat (gap n (i + 1))).
Proof.
  intros Hx. apply ltb_spec in Hx. unfold gap.
  assert (E1 : (φ (i + 1) = φ i + 1)%Z) by sia. rewrite E1. lia.
Qed.

Lemma merge_time x xC y yC src srcC mid midC hi hiC i iC j jC k kC dst dstC H HC :
  (cost (extract (extract (extract (extract (extract (extract (extract (extract (extract (merge_cost stepsCM x xC) y yC) src srcC) mid midC) hi hiC) i iC) j jC) k kC) dst dstC) H HC)
    <= Z.to_nat (gap hi k) * 200 + 10)%nat.
Proof.
  unfold merge_cost. cbn.
  match goal with |- context [@cost ?T (?G x xC y yC src srcC mid midC hi hiC i iC j jC k kC dst dstC H HC)] =>
    assert (HG : forall N i iC j jC k kC dst dstC H HC, (Z.to_nat (gap hi k) <= N)%nat ->
       (cost (G x xC y yC src srcC mid midC hi hiC i iC j jC k kC dst dstC H HC) <= Z.to_nat (gap hi k) * 200 + 10)%nat) end.
  { induction N as [N IH] using lt_wf_ind.
    intros i' iC' j' jC' k' kC' d' dC' [g] HC' HN.
    cost_simpl.
    pose proof (bdec_time (k' <? hi) (bool_w (k' <? hi))) as HB.
    cost_destruct (bdec (k' <? hi)); cost_simpl.
    - zero_partials. set_simpl.
      match goal with |- context [@cost ?T ?X] =>
        lazymatch X with extract (extract (extract (extract (extract (extract (take_left_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC) ?g ?gC =>
        let Hc := fresh "Htl" in
        pose proof (take_left_time a aC b bC c cC d dC e eC f fC g gC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc end end.
      pose proof (gap_S _ _ e) as E.
      assert (HN2 : (Z.to_nat (gap hi (k' + 1)) < N)%nat) by lia.
      cost_destruct (take_left x y src mid hi i' j'); cost_simpl; set_simpl;
      match goal with |- context [@cost ?T (?G' ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?i2 ?iC2 ?j2 ?jC2 (k' + 1)%uint63 ?kC2 ?d2 ?dC2 ?a ?e)] =>
        pose proof (IH _ HN2 i2 iC2 j2 jC2 (k' + 1)%uint63 kC2 d2 dC2 a e (le_n _)
          : (@cost T (G' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 i2 iC2 j2 jC2 (k' + 1)%uint63 kC2 d2 dC2 a e) <= _)%nat) as HI;
        revert HI; generalize (@cost T (G' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 i2 iC2 j2 jC2 (k' + 1)%uint63 kC2 d2 dC2 a e)); intros ? HI
      end; lia.
    - lia. }
  match goal with |- context [@cost ?T (?G x xC y yC src srcC mid midC hi hiC i iC j jC k kC dst dstC H HC)] =>
    exact (HG _ i iC j jC k kC dst dstC H HC (le_n _) : (@cost T (G x xC y yC src srcC mid midC hi hiC i iC j jC k kC dst dstC H HC) <= _)%nat) end.
Qed.

Ltac gen_min_merge :=
  repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | extract (min_i_cost stepsCM ?a ?aC) ?b ?bC =>
        let Hc := fresh "Hmin" in
        pose proof (min_i_time a aC b bC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    | extract (extract (extract (extract (extract (extract (extract (extract (extract (merge_cost stepsCM ?x ?xC) ?y ?yC) ?s ?sC) ?m ?mC) ?h ?hC) ?i ?iC) ?j ?jC) ?k ?kC) ?d ?dC) ?H ?HC =>
        let Hc := fresh "Hmerge" in
        pose proof (merge_time x xC y yC s sC m mC h hC i iC j jC k kC d dC H HC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    end end.

Lemma min_i_le a b : (φ (min_i a b) <= φ b)%Z.
Proof. unfold min_i. destruct (a <? b) eqn:E; [apply ltb_spec in E; lia | lia]. Qed.

Lemma pass_arith (lo hi n : int) N : (lo <? hi) = true -> (φ hi <= φ n)%Z ->
  (Z.to_nat (gap n lo) <= N)%nat ->
  (Z.to_nat (gap n hi) < N)%nat /\ (1 <= Z.to_nat (gap hi lo))%nat /\
  Z.to_nat (gap n lo) = (Z.to_nat (gap n hi) + Z.to_nat (gap hi lo))%nat.
Proof. intros H1 H2 H3. apply ltb_spec in H1. unfold gap in *. lia. Qed.

Lemma pass_time x xC y yC src srcC w wC n nC lo loC dst dstC H HC :
  (cost (extract (extract (extract (extract (extract (extract (extract (pass_cost stepsCM x xC) y yC) src srcC) w wC) n nC) lo loC) dst dstC) H HC)
    <= Z.to_nat (gap n lo) * 400 + 50)%nat.
Proof.
  unfold pass_cost. cbn.
  match goal with |- context [@cost ?T (?G x xC y yC src srcC w wC n nC lo loC dst dstC H HC)] =>
    assert (HG : forall N lo loC dst dstC H HC, (Z.to_nat (gap n lo) <= N)%nat ->
       (cost (G x xC y yC src srcC w wC n nC lo loC dst dstC H HC) <= Z.to_nat (gap n lo) * 400 + 50)%nat) end.
  { induction N as [N IH] using lt_wf_ind.
    intros lo' loC' d' dC' [g] HC' HN.
    cost_simpl.
    zero_partials. gen_min_merge.
    pose proof (bdec_time (lo' <? min_i (lo' + w + w) n) (bool_w (lo' <? min_i (lo' + w + w) n))) as HB.
    cost_destruct (bdec (lo' <? min_i (lo' + w + w) n)); cost_simpl.
    - zero_partials. gen_min_merge.
      destruct (pass_arith lo' (min_i (lo' + w + w) n) n N e (min_i_le _ _) HN) as (A1 & A2 & A3).
      match goal with |- context [@cost ?T (?G' ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?l2 ?lC2 ?d2 ?dC2 ?a ?e)] =>
        pose proof (IH _ A1 l2 lC2 d2 dC2 a e (le_n _)
          : (@cost T (G' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 l2 lC2 d2 dC2 a e) <= _)%nat) as HI;
        revert HI; generalize (@cost T (G' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 l2 lC2 d2 dC2 a e)); intros ? HI
      end. lia.
    - lia. }
  match goal with |- context [@cost ?T (?G x xC y yC src srcC w wC n nC lo loC dst dstC H HC)] =>
    exact (HG _ lo loC dst dstC H HC (le_n _) : (@cost T (G x xC y yC src srcC w wC n nC lo loC dst dstC H HC) <= _)%nat) end.
Qed.

Arguments andb_cost : simpl never.

Definition zn (x : int) : nat := Z.to_nat (φ x).
Arguments zn : simpl never.

Ltac gen_andb_pass :=
  repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | bdec_cost stepsCM ?a ?aC =>
        let Hc := fresh "Hbdec" in
        pose proof (bdec_time a aC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    | extract (andb_cost stepsCM ?a ?aC) ?b ?bC =>
        let Hc := fresh "Hand" in
        pose proof (andb_time a aC b bC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    | extract (extract (extract (extract (extract (extract (extract (pass_cost stepsCM ?x ?xC) ?y ?yC) ?s ?sC) ?w ?wC) ?n ?nC) ?l ?lC) ?d ?dC) ?H ?HC =>
        let Hc := fresh "Hpass" in
        pose proof (pass_time x xC y yC s sC w wC n nC l lC d dC H HC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    end end.

Lemma double_arith (w n : int) m : ((w <? n) && (w <? w + w)) = true ->
  (zn n <= 2 ^ S m * zn w)%nat -> (zn n <= 2 ^ m * zn (w + w))%nat.
Proof.
  intros H Hm. apply andb_prop in H. destruct H as [_ H]. rewrite ltb_spec in H.
  assert (E : φ (w + w) = (2 * φ w)%Z) by (revert H; pose proof (to_Z_bounded w); sia).
  unfold zn in *. rewrite E. rewrite Nat.pow_succ_r' in Hm. pose proof (to_Z_bounded w).
  replace (Z.to_nat (2 * φ w)) with (2 * Z.to_nat (φ w))%nat by lia. lia.
Qed.

Lemma double_base (w n : int) : ((w <? n) && (w <? w + w)) = true ->
  (zn n <= 2 ^ 0 * zn w)%nat -> False.
Proof.
  intros H Hm. apply andb_prop in H. destruct H as [H _]. rewrite ltb_spec in H.
  unfold zn in *. simpl in Hm. lia.
Qed.

Lemma gap_n0 n : Z.to_nat (gap n 0) = zn n.
Proof. unfold gap, zn. change (φ 0) with 0%Z. f_equal. lia. Qed.

Lemma sortl_time m x xC y yC n nC w wC src srcC dst dstC H HC :
  (zn n <= 2 ^ m * zn w)%nat ->
  (cost (extract (extract (extract (extract (extract (extract (sortl_cost stepsCM x xC) y yC) n nC) w wC) src srcC) dst dstC) H HC)
    <= m * (zn n * 400 + 100) + 50)%nat.
Proof.
  unfold sortl_cost. cbn.
  match goal with |- context [@cost ?T (?G x xC y yC n nC w wC src srcC dst dstC H HC)] =>
    assert (HG : forall m w wC src srcC dst dstC H HC, (zn n <= 2 ^ m * zn w)%nat ->
       (cost (G x xC y yC n nC w wC src srcC dst dstC H HC) <= m * (zn n * 400 + 100) + 50)%nat) end.
  { induction m0 as [|m' IH];
    intros w' wC' s' sC' d' dC' [g] HC' Hm;
    cost_simpl;
    zero_partials; gen_andb_pass;
    cost_destruct (bdec ((w' <? n) && (w' <? w' + w'))); cost_simpl.
    - exfalso. exact (double_base _ _ e Hm).
    - lia.
    - zero_partials. gen_andb_pass. rewrite gap_n0 in Hpass.
      pose proof (double_arith _ _ _ e Hm) as Hm'.
      match goal with |- context [@cost ?T (?G' ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?w2 ?wC2 ?s2 ?sC2 ?d2 ?dC2 ?a ?e)] =>
        pose proof (IH w2 wC2 s2 sC2 d2 dC2 a e Hm'
          : (@cost T (G' a1 a2 a3 a4 a5 a6 w2 wC2 s2 sC2 d2 dC2 a e) <= _)%nat) as HI;
        revert HI; generalize (@cost T (G' a1 a2 a3 a4 a5 a6 w2 wC2 s2 sC2 d2 dC2 a e)); intros ? HI
      end. lia.
    - lia. }
  intros Hm.
  match goal with |- context [@cost ?T (?G x xC y yC n nC w wC src srcC dst dstC H HC)] =>
    exact (HG m w wC src srcC dst dstC H HC Hm : (@cost T (G x xC y yC n nC w wC src srcC dst dstC H HC) <= _)%nat) end.
Qed.

Ltac gen_cross :=
  repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | bdec_cost stepsCM ?a ?aC =>
        let Hc := fresh "Hbdec" in
        pose proof (bdec_time a aC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    | extract (andb_cost stepsCM ?a ?aC) ?b ?bC =>
        let Hc := fresh "Hand" in
        pose proof (andb_time a aC b bC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    | extract (extract (extract (extract (cross_m_cost stepsCM ?x ?xC) ?y ?yC) ?a ?aC) ?b ?bC) ?c ?cC =>
        let Hc := fresh "Hcross" in
        pose proof (cross_m_time x xC y yC a aC b bC c cC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    end end.

Lemma zn_pred (lim k : int) b : ((lim <? k) && b) = true -> zn k = S (zn (k - 1)).
Proof.
  intros H. apply andb_prop in H. destruct H as [H _]. apply ltb_spec in H.
  pose proof (to_Z_bounded lim). unfold zn. assert (φ (k - 1) = φ k - 1)%Z by sia. lia.
Qed.

Arguments Uint63.to_Z : simpl never.
Arguments cross_m : simpl never.

Lemma pop_time x xC y yC st stC lim limC k kC q qC H HC :
  (cost (extract (extract (extract (extract (extract (extract (pop_cost stepsCM x xC) y yC) st stC) lim limC) k kC) q qC) H HC)
    + zn (pop x y st lim k q H) * 150 <= zn k * 150 + 150)%nat.
Proof.
  unfold pop_cost. cbn.
  match goal with |- context [@cost ?T (?G x xC y yC st stC lim limC k kC q qC H HC)] =>
    assert (HG : forall N k kC H HC, (zn k <= N)%nat ->
       (cost (G x xC y yC st stC lim limC k kC q qC H HC) + zn (pop x y st lim k q H) * 150 <= zn k * 150 + 150)%nat) end.
  { induction N as [|N IH]; intros k' kC' [g] HC' HN;
      cost_simpl; zero_partials; gen_cross;
      cost_destruct (bdec ((lim <? k') && lesb (cross_m x y st.[k' - 2] st.[k' - 1] q) 0)); cost_simpl.
    - exfalso. pose proof (zn_pred _ _ _ e). lia.
    - lia.
    - pose proof (zn_pred _ _ _ e) as Ez.
      assert (HN' : (zn (k' - 1) <= N)%nat) by lia.
      match goal with |- context [@cost ?T (?G' ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 (k' - 1)%uint63 ?w ?a9 ?a10 ?a ?e)] =>
        pose proof (IH (k' - 1)%uint63 w a e HN' : (@cost T (G' a1 a2 a3 a4 a5 a6 a7 a8 (k' - 1)%uint63 w a9 a10 a e) + _ <= _)%nat) as HI;
        revert HI; generalize (@cost T (G' a1 a2 a3 a4 a5 a6 a7 a8 (k' - 1)%uint63 w a9 a10 a e)); intros ? HI end.
      set (Rk := pop x y st lim (k' - 1) q _) in *. clearbody Rk. lia.
    - lia. }
  match goal with |- context [@cost ?T (?G x xC y yC st stC lim limC k kC q qC H HC)] =>
    exact (HG _ k kC H HC (le_n _) : (@cost T (G x xC y yC st stC lim limC k kC q qC H HC) + _ <= _)%nat) end.
Qed.


Lemma zn_succ_le k : (zn (k + 1) <= S (zn k))%nat.
Proof. unfold zn. pose proof (to_Z_bounded k). pose proof (to_Z_bounded (k + 1)).
  rewrite add_spec. change (φ 1) with 1%Z.
  destruct (Z.eq_dec (φ k + 1) wB) as [E|E].
  - rewrite E, Z_mod_same_full. lia.
  - rewrite Z.mod_small; lia. Qed.

Ltac gen_pop :=
  repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | bdec_cost stepsCM ?a ?aC =>
        let Hc := fresh "Hbdec" in
        pose proof (bdec_time a aC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    | extract (extract (extract (extract (extract (extract (pop_cost stepsCM ?x ?xC) ?y ?yC) ?s ?sC) ?l ?lC) ?k ?kC) ?q ?qC) ?H ?HC =>
        let Hc := fresh "Hpop" in
        pose proof (pop_time x xC y yC s sC l lC k kC q qC H HC : (@cost T X + _ <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    end end.

Lemma lower_time x xC y yC ord ordC st stC n nC k kC i iC H HC :
  (cost (extract (extract (extract (extract (extract (extract (extract (lower_cost stepsCM x xC) y yC) ord ordC) st stC) n nC) k kC) i iC) H HC)
    <= Z.to_nat (gap n i) * 400 + zn k * 150 + 50)%nat.
Proof.
  unfold lower_cost. cbn.
  match goal with |- context [@cost ?T (?G x xC y yC ord ordC st stC n nC k kC i iC H HC)] =>
    assert (HG : forall N st stC k kC i iC H HC, (Z.to_nat (gap n i) <= N)%nat ->
       (cost (G x xC y yC ord ordC st stC n nC k kC i iC H HC) <= Z.to_nat (gap n i) * 400 + zn k * 150 + 50)%nat) end.
  { induction N as [N IH] using lt_wf_ind.
    intros s' sC' k' kC' i' iC' [g] HC' HN.
    cost_simpl. zero_partials. gen_pop.
    cost_destruct (bdec (i' <? n)); cost_simpl.
    - zero_partials. set_simpl. gen_pop.
      pose proof (gap_S _ _ e) as E.
      assert (HN2 : (Z.to_nat (gap n (i' + 1)) < N)%nat) by lia.
      set (k2 := pop x y s' 1 k' ord.[i'] _) in *.
      pose proof (zn_succ_le k2).
      match goal with |- context [@cost ?T (?G' ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?s2 ?sC2 ?a7 ?a8 ?k3 ?kC3 ?i2 ?iC2 ?a ?e)] =>
        pose proof (IH _ HN2 s2 sC2 k3 kC3 i2 iC2 a e (le_n _)
          : (@cost T (G' a1 a2 a3 a4 a5 a6 s2 sC2 a7 a8 k3 kC3 i2 iC2 a e) <= _)%nat) as HI;
        revert HI; generalize (@cost T (G' a1 a2 a3 a4 a5 a6 s2 sC2 a7 a8 k3 kC3 i2 iC2 a e)); intros ? HI
      end.
      clearbody k2. lia.
    - zero_pairs. lia. }
  match goal with |- context [@cost ?T (?G x xC y yC ord ordC st stC n nC k kC i iC H HC)] =>
    exact (HG _ st stC k kC i iC H HC (le_n _) : (@cost T (G x xC y yC ord ordC st stC n nC k kC i iC H HC) <= _)%nat) end.
Qed.

Lemma zn_down (j : int) : (0 <? j) = true -> zn j = S (zn (j - 1)).
Proof. intros H. apply ltb_spec in H. change (φ 0) with 0%Z in H. unfold zn. assert (φ (j - 1) = φ j - 1)%Z by sia. lia. Qed.

Lemma upper_time x xC y yC ord ordC st stC lim limC k kC j jC H HC :
  (cost (extract (extract (extract (extract (extract (extract (extract (upper_cost stepsCM x xC) y yC) ord ordC) st stC) lim limC) k kC) j jC) H HC)
    <= zn j * 400 + zn k * 150 + 50)%nat.
Proof.
  unfold upper_cost. cbn.
  match goal with |- context [@cost ?T (?G x xC y yC ord ordC st stC lim limC k kC j jC H HC)] =>
    assert (HG : forall N st stC k kC j jC H HC, (zn j <= N)%nat ->
       (cost (G x xC y yC ord ordC st stC lim limC k kC j jC H HC) <= zn j * 400 + zn k * 150 + 50)%nat) end.
  { induction N as [N IH] using lt_wf_ind.
    intros s' sC' k' kC' j' jC' [g] HC' HN.
    cost_simpl. zero_partials. gen_pop.
    cost_destruct (bdec (0 <? j')); cost_simpl.
    - zero_partials. set_simpl. gen_pop.
      pose proof (zn_down _ e) as E.
      assert (HN2 : (zn (j' - 1) < N)%nat) by lia.
      set (k2 := pop x y s' lim k' ord.[j' - 1] _) in *.
      pose proof (zn_succ_le k2).
      match goal with |- context [@cost ?T (?G' ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?s2 ?sC2 ?a7 ?a8 ?k3 ?kC3 ?i2 ?iC2 ?a ?e)] =>
        pose proof (IH _ HN2 s2 sC2 k3 kC3 i2 iC2 a e (le_n _)
          : (@cost T (G' a1 a2 a3 a4 a5 a6 s2 sC2 a7 a8 k3 kC3 i2 iC2 a e) <= _)%nat) as HI;
        revert HI; generalize (@cost T (G' a1 a2 a3 a4 a5 a6 s2 sC2 a7 a8 k3 kC3 i2 iC2 a e)); intros ? HI
      end.
      clearbody k2. lia.
    - zero_pairs. lia. }
  match goal with |- context [@cost ?T (?G x xC y yC ord ordC st stC lim limC k kC j jC H HC)] =>
    exact (HG _ st stC k kC j jC H HC (le_n _) : (@cost T (G x xC y yC ord ordC st stC lim limC k kC j jC H HC) <= _)%nat) end.
Qed.

Lemma copyl_time src srcC dst dstC h hC i iC H HC :
  (cost (extract (extract (extract (extract (copyl_cost stepsCM src srcC) dst dstC) h hC) i iC) H HC)
    <= Z.to_nat (gap h i) * 50 + 20)%nat.
Proof.
  unfold copyl_cost. cbn.
  match goal with |- context [@cost ?T (?G src srcC dst dstC h hC i iC H HC)] =>
    assert (HG : forall N dst dstC i iC H HC, (Z.to_nat (gap h i) <= N)%nat ->
       (cost (G src srcC dst dstC h hC i iC H HC) <= Z.to_nat (gap h i) * 50 + 20)%nat) end.
  { induction N as [N IH] using lt_wf_ind.
    intros d' dC' i' iC' [g] HC' HN.
    cost_simpl. zero_partials. gen_pop.
    cost_destruct (bdec (i' <? h)); cost_simpl.
    - zero_partials. set_simpl. gen_pop.
      pose proof (gap_S _ _ e) as E.
      assert (HN2 : (Z.to_nat (gap h (i' + 1)) < N)%nat) by lia.
      match goal with |- context [@cost ?T (?G' ?a1 ?a2 ?d2 ?dC2 ?a3 ?a4 ?i2 ?iC2 ?a ?e)] =>
        pose proof (IH _ HN2 d2 dC2 i2 iC2 a e (le_n _)
          : (@cost T (G' a1 a2 d2 dC2 a3 a4 i2 iC2 a e) <= _)%nat) as HI;
        revert HI; generalize (@cost T (G' a1 a2 d2 dC2 a3 a4 i2 iC2 a e)); intros ? HI
      end.
      lia.
    - lia. }
  match goal with |- context [@cost ?T (?G src srcC dst dstC h hC i iC H HC)] =>
    exact (HG _ dst dstC i iC H HC (le_n _) : (@cost T (G src srcC dst dstC h hC i iC H HC) <= _)%nat) end.
Qed.

Lemma initl_time n nC i iC a aC H HC :
  (cost (extract (extract (extract (initl_cost stepsCM n nC) i iC) a aC) H HC)
    <= Z.to_nat (gap n i) * 50 + 20)%nat.
Proof.
  unfold initl_cost. cbn.
  match goal with |- context [@cost ?T (?G n nC i iC a aC H HC)] =>
    assert (HG : forall N i iC a aC H HC, (Z.to_nat (gap n i) <= N)%nat ->
       (cost (G n nC i iC a aC H HC) <= Z.to_nat (gap n i) * 50 + 20)%nat) end.
  { induction N as [N IH] using lt_wf_ind.
    intros i' iC' d' dC' [g] HC' HN.
    cost_simpl. zero_partials. gen_pop.
    cost_destruct (bdec (i' <? n)); cost_simpl.
    - zero_partials. set_simpl. gen_pop.
      pose proof (gap_S _ _ e) as E.
      assert (HN2 : (Z.to_nat (gap n (i' + 1)) < N)%nat) by lia.
      match goal with |- context [@cost ?T (?G' ?a1 ?a2 ?i2 ?iC2 ?d2 ?dC2 ?a ?e)] =>
        pose proof (IH _ HN2 i2 iC2 d2 dC2 a e (le_n _)
          : (@cost T (G' a1 a2 i2 iC2 d2 dC2 a e) <= _)%nat) as HI;
        revert HI; generalize (@cost T (G' a1 a2 i2 iC2 d2 dC2 a e)); intros ? HI
      end.
      lia.
    - lia. }
  match goal with |- context [@cost ?T (?G n nC i iC a aC H HC)] =>
    exact (HG _ i iC a aC H HC (le_n _) : (@cost T (G n nC i iC a aC H HC) <= _)%nat) end.
Qed.


Ltac make_simpl :=
  repeat match goal with
  | |- context [cost (extract (extract (make_cost ?a ?b ?c) ?d ?e) ?f ?g)] =>
      change (cost (extract (extract (make_cost a b c) d e) f g)) with 1%nat
  end.

Ltac gen_ms :=
  repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | bdec_cost stepsCM ?a ?aC =>
        let Hc := fresh "Hbdec" in
        pose proof (bdec_time a aC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    | extract (andb_cost stepsCM ?a ?aC) ?b ?bC =>
        let Hc := fresh "Hand" in
        pose proof (andb_time a aC b bC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    | extract (extract (extract (initl_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC =>
        let Hc := fresh "Hinit" in
        pose proof (initl_time a aC b bC c cC d dC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    end end.

Lemma log2_cover (N : nat) : (N <= 2 ^ (Nat.log2 N + 1) * 1)%nat.
Proof.
  rewrite Nat.mul_1_r, Nat.add_1_r. destruct N as [|N']; [simpl; lia|].
  pose proof (Nat.log2_spec (S N') ltac:(lia)). lia.
Qed.

Lemma zn1 : zn 1 = 1%nat.
Proof. reflexivity. Qed.

Lemma msort_time x xC y yC n nC :
  (cost (extract (extract (msort_cost stepsCM x xC) y yC) n nC)
    <= (Nat.log2 (zn n) + 1) * (zn n * 400 + 100) + zn n * 50 + 200)%nat.
Proof.
  unfold msort_cost. cost_simpl. zero_partials. make_simpl. gen_ms.
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with extract (extract (extract (extract (extract (extract (sortl_cost stepsCM ?x ?xC) ?y ?yC) ?n ?nC) ?w ?wC) ?s ?sC) ?d ?dC) ?H ?HC =>
    let Hc := fresh "Hsortl" in
    pose proof (sortl_time (Nat.log2 (zn n) + 1) x xC y yC n nC w wC s sC d dC H HC ltac:(rewrite zn1; apply log2_cover) : (@cost T X <= _)%nat) as Hc;
    revert Hc; generalize (@cost T X); intros ? Hc end end.
  rewrite gap_n0 in Hinit. lia.
Qed.


Ltac gen_all :=
  repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | bdec_cost stepsCM ?a ?aC =>
        let Hc := fresh "Hbdec" in
        pose proof (bdec_time a aC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    | extract (andb_cost stepsCM ?a ?aC) ?b ?bC =>
        let Hc := fresh "Hand" in
        pose proof (andb_time a aC b bC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    | extract (extract (msort_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC =>
        let Hc := fresh "Hms" in
        pose proof (msort_time a aC b bC c cC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    | extract (extract (extract (extract (extract (extract (extract (lower_cost stepsCM ?x ?xC) ?y ?yC) ?o ?oC) ?s ?sC) ?n ?nC) ?k ?kC) ?i ?iC) ?H ?HC =>
        let Hc := fresh "Hlow" in
        pose proof (lower_time x xC y yC o oC s sC n nC k kC i iC H HC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    | extract (extract (extract (extract (extract (extract (extract (upper_cost stepsCM ?x ?xC) ?y ?yC) ?o ?oC) ?s ?sC) ?n ?nC) ?k ?kC) ?i ?iC) ?H ?HC =>
        let Hc := fresh "Hup" in
        pose proof (upper_time x xC y yC o oC s sC n nC k kC i iC H HC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    | extract (extract (extract (extract (copyl_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC =>
        let Hc := fresh "Hcopy" in
        pose proof (copyl_time a aC b bC c cC d dC e eC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    end end.

Lemma facts_zn (n l k : int) : (φ l <= φ n)%Z -> (1 <= φ k <= 2 * φ n)%Z ->
  (zn l <= zn n)%nat /\ (Z.to_nat (gap (k - 1) 0) <= 2 * zn n)%nat.
Proof.
  intros H1 H2. unfold zn, gap. change (φ 0) with 0%Z.
  assert (φ (k - 1) = φ k - 1)%Z by sia. lia.
Qed.

Lemma lower_init n : (1 <= φ n)%Z ->
  (Z.to_nat (gap n 1) <= zn n)%nat /\ zn 1 = 1%nat /\ (zn (n - 1) <= zn n)%nat.
Proof.
  intros Hn. unfold gap, zn. change (φ 1) with 1%Z. pose proof (to_Z_bounded n).
  assert (φ (n - 1) = φ n - 1)%Z by sia. split; [lia|]. split; [reflexivity|]. lia.
Qed.

Lemma valid_len (xs ys : list Z) (x : array sint) : valid_input xs ys -> repr x xs -> (1 <= φ (length x))%Z.
Proof.
  intros [Hn _ _ _] Hx. rewrite (repr_len_s x xs Hx). unfold len in Hn. lia.
Qed.

Ltac fix_len x VL :=
  match goal with Hms : context [Nat.log2 (zn ?L)] |- _ =>
    let I := fresh "I" in pose proof (lower_init L VL) as I;
    let N := fresh "NN" in set (N := zn L) in *; change (zn (length x)) with N;
    repeat match goal with H : context [zn (length x)] |- _ => change (zn (length x)) with N in H end end.

Lemma hull_time (xs ys : list Z) (x y : array sint) xC yC :
  valid_input xs ys -> repr x xs -> repr y ys ->
  (cost (extract (hull_cost stepsCM x xC) y yC)
    <= (Nat.log2 (zn (length x)) + 1) * (zn (length x) * 400 + 100) + zn (length x) * 2000 + 1000)%nat.
Proof.
  intros Hv Hx Hy.
  pose proof (valid_len xs ys x Hv Hx) as VL.
  unfold hull_cost. cost_simpl. zero_partials. make_simpl. gen_all.
  match goal with |- context [extract (andb_cost stepsCM ?a ?aC) ?b ?bC] => generalize (extract (andb_cost stepsCM a aC) b bC) end.
  destruct ((x.[(msort x y (length x)).[0]] =? x.[(msort x y (length x)).[length x - 1]]) && (y.[(msort x y (length x)).[0]] =? y.[(msort x y (length x)).[length x - 1]])) eqn:Edeg; intros wd.
  { match goal with |- context [@cost ?T (?c, ?w)] => change (@cost T (c, w)) with c end. fix_len x VL. lia. }
  cost_simpl. zero_partials. make_simpl. set_simpl. gen_all.
  cost_destruct_witness (lower x y (msort x y (length x)) (make (length x + length x) 0).[0 <- (msort x y (length x)).[0]] (length x) 1 1 (Zwf_well_founded 0 (gap (length x) 1))) as [st1 st1C l lC] eqn:EL.
  cost_simpl. zero_partials. gen_all.
  cost_destruct_witness (upper x y (msort x y (length x)) st1 l l (length x - 1) (Zwf_well_founded 0 (φ (length x - 1)))) as [st2 st2C k kC] eqn:EU.
  cost_simpl. zero_partials. make_simpl. gen_all.
  pose proof (hull_facts xs ys x y Hv Hx Hy) as HF. cbv zeta in HF.
  destruct (HF Edeg st1 l EL) as [F1 F2].
  destruct (facts_zn _ _ _ F1 (F2 st2 k EU)) as [Z1 Z2].
  fix_len x VL. clear HF F2. lia.
Qed.

Theorem convex_hull_time : exists c1 c2 : nat,
  forall (x_coordinates y_coordinates : list Z)
  (x_coordinates_arr y_coordinates_arr : array sint),
  valid_input x_coordinates y_coordinates ->
  repr x_coordinates_arr x_coordinates ->
  repr y_coordinates_arr y_coordinates ->
  (cost2 convex_hull_cost x_coordinates_arr y_coordinates_arr <= c1 * ((size x_coordinates_arr + 1) * (Nat.log2 (size x_coordinates_arr) + 1)) + c2)%nat.
Proof.
  exists 3000%nat, 1000%nat. intros xs ys x y Hv Hx Hy.
  remember (3000 * ((size x + 1) * (Nat.log2 (size x) + 1)) + 1000)%nat as R eqn:ER.
  unfold cost2, convex_hull_cost. rewrite call_cost2_eq. cost_simpl.
  change (cost (hull_cost stepsCM x (witness x))) with 0%nat.
  pose proof (hull_time xs ys x y (witness x) (witness y) Hv Hx Hy) as H.
  change (zn (length x)) with (size x) in H.
  subst R. generalize dependent (size x). intros N H. rewrite Nat.add_0_l. eapply Nat.le_trans; [exact H|]. clear. nia.
Qed.
