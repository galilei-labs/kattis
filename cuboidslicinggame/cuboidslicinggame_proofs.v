(* Correctness proofs for cuboidslicinggame_implem.v. *)
From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Btauto.
Import ListNotations.

Unset Lia Cache.

Require Export cuboidslicinggame_implem.



(* ================================================================== *)
(* Part A. The Sprague-Grundy theorem, on the math side               *)
(* ================================================================== *)

Section MathSide.
Local Open Scope N_scope.

Definition Gc (g : N -> N -> N -> N) (c : cuboid) : N :=
  let '(x, y, z) := c in g x y z.

Definition xorG (g : N -> N -> N -> N) (p : position) : N :=
  fold_right (fun c acc => N.lxor (Gc g c) acc) 0 p.

Lemma xorG_app : forall g l m, xorG g (l ++ m) = N.lxor (xorG g l) (xorG g m).
Proof.
  intros g l m. induction l as [|c l IH]; simpl.
  - reflexivity.
  - rewrite IH, N.lxor_assoc. reflexivity.
Qed.

(* The eight sub-cuboids of a cut, in the order of [pieces]. *)
Definition L8 (p1 p2 q1 q2 r1 r2 : N) : position :=
  [(p1,q1,r1); (p1,q1,r2); (p1,q2,r1); (p1,q2,r2);
   (p2,q1,r1); (p2,q1,r2); (p2,q2,r1); (p2,q2,r2)].

Definition C8 g (p1 p2 q1 q2 r1 r2 : N) : N := xorG g (L8 p1 p2 q1 q2 r1 r2).

Definition cutval g (x y z a b c : N) : N :=
  C8 g (a - 1) (x - a) (b - 1) (y - b) (c - 1) (z - c).

Definition fullS g (x y z : N) (t : N) : Prop :=
  exists a b c, 1 <= a <= x /\ 1 <= b <= y /\ 1 <= c <= z /\ cutval g x y z a b c = t.

Definition halfS g (x y z : N) (t : N) : Prop :=
  exists a b c, 1 <= a <= (x + 1) / 2 /\ 1 <= b <= (y + 1) / 2 /\
                1 <= c <= (z + 1) / 2 /\ cutval g x y z a b c = t.

Definition mexprop (S : N -> Prop) (v : N) : Prop :=
  ~ S v /\ forall t, t < v -> S t.

Definition posf (c : cuboid) : bool :=
  let '(p, q, r) := c in ((0 <? p) && (0 <? q) && (0 <? r))%bool.

Lemma pieces_unf : forall x y z a b c,
  pieces x y z a b c = filter posf (L8 (a - 1) (x - a) (b - 1) (y - b) (c - 1) (z - c)).
Proof. reflexivity. Qed.

Lemma posf_true : forall p q r, posf (p, q, r) = true -> 0 < p /\ 0 < q /\ 0 < r.
Proof.
  intros p q r H. simpl in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  rewrite N.ltb_lt in H1, H2, H3. auto.
Qed.

Lemma posf_false : forall p q r, posf (p, q, r) = false -> p = 0 \/ q = 0 \/ r = 0.
Proof.
  intros p q r H. simpl in H.
  destruct (0 <? p) eqn:E1; [|left; rewrite N.ltb_ge in E1; lia].
  destruct (0 <? q) eqn:E2; [|right; left; rewrite N.ltb_ge in E2; lia].
  destruct (0 <? r) eqn:E3; [|right; right; rewrite N.ltb_ge in E3; lia].
  discriminate.
Qed.

Lemma L8_in : forall p1 p2 q1 q2 r1 r2 p q r,
  In (p, q, r) (L8 p1 p2 q1 q2 r1 r2) ->
  (p = p1 \/ p = p2) /\ (q = q1 \/ q = q2) /\ (r = r1 \/ r = r2).
Proof.
  intros p1 p2 q1 q2 r1 r2 p q r H. cbn in H.
  repeat destruct H as [H | H];
    try (injection H; intros; subst; tauto); contradiction.
Qed.

Lemma xorG_filter : forall g f l,
  (forall c, In c l -> f c = false -> Gc g c = 0) ->
  xorG g (filter f l) = xorG g l.
Proof.
  intros g f l. induction l as [|c l IH]; intros H; simpl; [reflexivity|].
  destruct (f c) eqn:E; simpl.
  - rewrite IH; [reflexivity|]. intros c' Hc'. apply H. right. exact Hc'.
  - rewrite H by (auto; left; reflexivity). rewrite N.lxor_0_l.
    apply IH. intros c' Hc'. apply H. right. exact Hc'.
Qed.

Definition vol (p : position) : N :=
  fold_right (fun c acc => let '(x, y, z) := c in x * y * z + acc) 0 p.

Lemma vol_app : forall l m, vol (l ++ m) = vol l + vol m.
Proof.
  intros l m. induction l as [|[[x y] z] l IH]; simpl; [reflexivity|].
  rewrite IH. lia.
Qed.

Lemma vol_filter : forall f l, vol (filter f l) <= vol l.
Proof.
  intros f l. induction l as [|[[x y] z] l IH]; simpl; [lia|].
  destruct (f (x, y, z)); simpl; lia.
Qed.

Lemma vol_pieces : forall x y z a b c,
  1 <= a <= x -> 1 <= b <= y -> 1 <= c <= z ->
  vol (pieces x y z a b c) < x * y * z.
Proof.
  intros x y z a b c Ha Hb Hc. rewrite pieces_unf.
  eapply N.le_lt_trans; [apply vol_filter|].
  cbn [vol L8 fold_right].
  set (p1 := a - 1). set (p2 := x - a). set (q1 := b - 1). set (q2 := y - b).
  set (r1 := c - 1). set (r2 := z - c).
  assert (Ex : x = p1 + p2 + 1) by lia.
  assert (Ey : y = q1 + q2 + 1) by lia.
  assert (Ez : z = r1 + r2 + 1) by lia.
  rewrite Ex, Ey, Ez. clearbody p1 p2 q1 q2 r1 r2.
  nia.
Qed.

Lemma move_vol : forall p q, move p q -> vol q < vol p.
Proof.
  intros p q H. destruct H as [l r x y z a b c Ha Hb Hc].
  rewrite !vol_app. simpl. pose proof (vol_pieces x y z a b c Ha Hb Hc). lia.
Qed.

Lemma wins_loses_excl : forall p, wins p -> loses p -> False.
Proof.
  intros p.
  induction p as [p IH] using
    (well_founded_induction (well_founded_ltof _ (fun p => N.to_nat (vol p)))).
  intros Hw Hl. destruct Hw as [p q Hm Hlq].
  destruct Hl as [p Hall].
  apply (IH q); [| apply Hall; exact Hm | exact Hlq].
  unfold ltof. pose proof (move_vol _ _ Hm). lia.
Qed.

Definition bounded (M : N) (p : position) : Prop :=
  forall x y z, In (x, y, z) p -> 1 <= x <= M /\ 1 <= y <= M /\ 1 <= z <= M.

Lemma move_bounded : forall M p q, bounded M p -> move p q -> bounded M q.
Proof.
  intros M p q Hb H. destruct H as [l r x y z a b c Ha Hb' Hc].
  assert (Hx : 1 <= x <= M /\ 1 <= y <= M /\ 1 <= z <= M)
    by (apply Hb; apply in_or_app; right; left; reflexivity).
  intros u v w Hin. apply in_app_iff in Hin as [Hin | Hin].
  - apply Hb. apply in_or_app. left. exact Hin.
  - apply in_app_iff in Hin as [Hin | Hin].
    + rewrite pieces_unf in Hin. apply filter_In in Hin as [Hin Hf].
      apply posf_true in Hf. apply L8_in in Hin. lia.
    + apply Hb. apply in_or_app. right. right. exact Hin.
Qed.

Lemma xor_bit_elem : forall g p k, N.testbit (xorG g p) k = true ->
  exists c, In c p /\ N.testbit (Gc g c) k = true.
Proof.
  intros g p k. induction p as [|c p IH]; simpl; intros H.
  - discriminate.
  - rewrite N.lxor_spec in H.
    destruct (N.testbit (Gc g c) k) eqn:E.
    + exists c. auto.
    + simpl in H. destruct (IH H) as (c' & H1 & H2). exists c'. auto.
Qed.

Lemma lxor_lt : forall u s, s <> 0 -> N.testbit u (N.log2 s) = true ->
  N.lxor u s < u.
Proof.
  intros u s Hs Hu. set (k := N.log2 s) in *.
  set (w := N.lxor u s).
  assert (Hsk : N.testbit s k = true) by (apply N.bit_log2; exact Hs).
  assert (Hwk : N.testbit w k = false)
    by (unfold w; rewrite N.lxor_spec, Hu, Hsk; reflexivity).
  assert (Hsh : N.shiftr w (k + 1) = N.shiftr u (k + 1)).
  { apply N.bits_inj. intro n. rewrite !N.shiftr_spec'. unfold w.
    rewrite N.lxor_spec.
    rewrite (N.bits_above_log2 s) by (unfold k; lia).
    apply Bool.xorb_false_r. }
  rewrite !N.shiftr_div_pow2 in Hsh.
  assert (Hp : 2 ^ (k + 1) = 2 * 2 ^ k) by (rewrite N.pow_add_r; lia).
  assert (Hpk : 0 < 2 ^ k) by (apply N.neq_0_lt_0; apply N.pow_nonzero; lia).
  assert (Hrw : w mod 2 ^ (k + 1) < 2 ^ k).
  { destruct (N.lt_ge_cases (w mod 2 ^ (k + 1)) (2 ^ k)) as [H|H]; [exact H|].
    exfalso.
    assert (Hr1 : w mod 2 ^ (k + 1) < 2 ^ (k + 1)) by (apply N.mod_lt; lia).
    assert (Hl1 : k <= N.log2 (w mod 2 ^ (k + 1)))
      by (apply N.log2_le_pow2; lia).
    assert (Hl2 : N.log2 (w mod 2 ^ (k + 1)) < k + 1)
      by (apply N.log2_lt_pow2; lia).
    assert (Hb : N.testbit (w mod 2 ^ (k + 1)) (N.log2 (w mod 2 ^ (k + 1))) = true)
      by (apply N.bit_log2; lia).
    replace (N.log2 (w mod 2 ^ (k + 1))) with k in Hb by lia.
    rewrite N.mod_pow2_bits_low in Hb by lia. congruence. }
  assert (Hru : 2 ^ k <= u mod 2 ^ (k + 1)).
  { destruct (N.lt_ge_cases (u mod 2 ^ (k + 1)) (2 ^ k)) as [H|H]; [|exact H].
    exfalso.
    assert (Hb : N.testbit (u mod 2 ^ (k + 1)) k = false).
    { destruct (N.eq_0_gt_0_cases (u mod 2 ^ (k + 1))) as [E|E].
      - rewrite E. apply N.bits_0.
      - apply N.bits_above_log2. apply N.log2_lt_pow2; lia. }
    rewrite N.mod_pow2_bits_low in Hb by lia. congruence. }
  pose proof (N.div_mod w (2 ^ (k + 1)) ltac:(lia)) as Dw.
  pose proof (N.div_mod u (2 ^ (k + 1)) ltac:(lia)) as Du.
  rewrite Hsh in Dw.
  set (Q := 2 ^ (k + 1) * (u / 2 ^ (k + 1))) in *.
  set (rw := w mod 2 ^ (k + 1)) in *. set (ru := u mod 2 ^ (k + 1)) in *.
  clearbody Q rw ru w. clear - Dw Du Hrw Hru. lia.
Qed.

Section SG.
Variables (M : N) (g : N -> N -> N -> N).
Hypothesis Hg0 : forall x y z, x <= M -> y <= M -> z <= M ->
  (x = 0 \/ y = 0 \/ z = 0) -> g x y z = 0.
Hypothesis Hmex : forall x y z, 1 <= x <= M -> 1 <= y <= M -> 1 <= z <= M ->
  mexprop (fullS g x y z) (g x y z).

Lemma xorG_pieces : forall x y z a b c,
  x <= M -> y <= M -> z <= M -> 1 <= a <= x -> 1 <= b <= y -> 1 <= c <= z ->
  xorG g (pieces x y z a b c) = cutval g x y z a b c.
Proof.
  intros x y z a b c Hx Hy Hz Ha Hb Hc. rewrite pieces_unf, xorG_filter; [reflexivity|].
  intros [[p q] r] Hin Hf. simpl. apply L8_in in Hin. apply posf_false in Hf.
  apply Hg0; lia.
Qed.

Theorem sprague_grundy : forall p, bounded M p ->
  (xorG g p <> 0 -> wins p) /\ (xorG g p = 0 -> loses p).
Proof.
  intros p.
  induction p as [p IH] using
    (well_founded_induction (well_founded_ltof _ (fun p => N.to_nat (vol p)))).
  intros Hb. split.
  - intros Hs.
    destruct (xor_bit_elem g p (N.log2 (xorG g p)) (N.bit_log2 _ Hs))
      as ([[x y] z] & Hin & Hc).
    simpl in Hc.
    destruct (Hb x y z Hin) as (Bx & By & Bz).
    destruct (Hmex x y z Bx By Bz) as [_ Hall].
    destruct (Hall (N.lxor (g x y z) (xorG g p)) (lxor_lt _ _ Hs Hc))
      as (a & b & c & Ha & Hb' & Hc' & Hv).
    destruct (in_split _ _ Hin) as (l & r & Hp).
    assert (Hm : move p (l ++ pieces x y z a b c ++ r))
      by (rewrite Hp; constructor; auto).
    apply wins_move with (next_state := l ++ pieces x y z a b c ++ r); [exact Hm|].
    pose proof (move_vol _ _ Hm) as Hvol.
    apply (proj2 (IH (l ++ pieces x y z a b c ++ r) ltac:(unfold ltof; lia)
             (move_bounded _ _ _ Hb Hm))).
    assert (Es : xorG g p = N.lxor (xorG g l) (N.lxor (g x y z) (xorG g r)))
      by (rewrite Hp, xorG_app; reflexivity).
    rewrite !xorG_app, xorG_pieces, Hv, Es by lia.
    apply N.bits_inj_0. intro n. rewrite !N.lxor_spec. btauto.
  - intros H0. constructor. intros q Hm.
    pose proof (move_vol _ _ Hm) as Hv.
    pose proof (move_bounded _ _ _ Hb Hm) as Hbq.
    apply (proj1 (IH q ltac:(unfold ltof; lia) Hbq)).
    clear IH Hv Hbq.
    destruct Hm as [l r x y z a b c Ha Hb' Hc].
    destruct (Hb x y z ltac:(apply in_or_app; right; left; reflexivity))
      as (Bx & By & Bz).
    destruct (Hmex x y z Bx By Bz) as [Hn _].
    intro Hq. apply Hn. exists a, b, c. do 3 (split; [assumption|]).
    rewrite !xorG_app, xorG_pieces in Hq by lia.
    rewrite xorG_app in H0. simpl in H0.
    set (cv := cutval g x y z a b c) in *.
    assert (E1 : cv = N.lxor (N.lxor (xorG g l) (N.lxor cv (xorG g r)))
                              (N.lxor (xorG g l) (xorG g r)))
      by (apply N.bits_inj; intro n; rewrite !N.lxor_spec; btauto).
    assert (E2 : g x y z = N.lxor (N.lxor (xorG g l) (N.lxor (g x y z) (xorG g r)))
                              (N.lxor (xorG g l) (xorG g r)))
      by (apply N.bits_inj; intro n; rewrite !N.lxor_spec; btauto).
    rewrite Hq in E1. rewrite H0 in E2. congruence.
Qed.

End SG.
End MathSide.

(* ================================================================== *)
(* Part B. Symmetries of a cut: mirroring and permutation of the axes *)
(* ================================================================== *)

Section Symmetries.
Local Open Scope N_scope.

Ltac xbits := apply N.bits_inj; intro; rewrite ?N.lxor_spec, ?N.bits_0; btauto.

Lemma C8_ext : forall g h p1 p2 q1 q2 r1 r2,
  (forall p q r, (p = p1 \/ p = p2) -> (q = q1 \/ q = q2) -> (r = r1 \/ r = r2) ->
     g p q r = h p q r) ->
  C8 g p1 p2 q1 q2 r1 r2 = C8 h p1 p2 q1 q2 r1 r2.
Proof.
  intros g h p1 p2 q1 q2 r1 r2 H. cbn [C8 L8 xorG fold_right Gc].
  rewrite !H by first [left; reflexivity | right; reflexivity]. reflexivity.
Qed.

Lemma C8_perm_P : forall g p1 p2 q1 q2 r1 r2,
  C8 g p2 p1 q1 q2 r1 r2 = C8 g p1 p2 q1 q2 r1 r2.
Proof. intros. cbn [C8 L8 xorG fold_right Gc]. xbits. Qed.

Lemma C8_perm_Q : forall g p1 p2 q1 q2 r1 r2,
  C8 g p1 p2 q2 q1 r1 r2 = C8 g p1 p2 q1 q2 r1 r2.
Proof. intros. cbn [C8 L8 xorG fold_right Gc]. xbits. Qed.

Lemma C8_perm_R : forall g p1 p2 q1 q2 r1 r2,
  C8 g p1 p2 q1 q2 r2 r1 = C8 g p1 p2 q1 q2 r1 r2.
Proof. intros. cbn [C8 L8 xorG fold_right Gc]. xbits. Qed.

Lemma C8_tr12 : forall g h p1 p2 q1 q2 r1 r2,
  (forall p q r, h q p r = g p q r) ->
  C8 h q1 q2 p1 p2 r1 r2 = C8 g p1 p2 q1 q2 r1 r2.
Proof. intros g h p1 p2 q1 q2 r1 r2 H. cbn [C8 L8 xorG fold_right Gc]. rewrite !H. xbits. Qed.

Lemma C8_tr23 : forall g h p1 p2 q1 q2 r1 r2,
  (forall p q r, h p r q = g p q r) ->
  C8 h p1 p2 r1 r2 q1 q2 = C8 g p1 p2 q1 q2 r1 r2.
Proof. intros g h p1 p2 q1 q2 r1 r2 H. cbn [C8 L8 xorG fold_right Gc]. rewrite !H. xbits. Qed.

Lemma fullS_sym12 : forall g, (forall p q r, g q p r = g p q r) ->
  forall x y z t, fullS g y x z t <-> fullS g x y z t.
Proof.
  intros g Hs x y z t. split; intros (a & b & c & Ha & Hb & Hc & E);
    exists b, a, c; do 3 (split; [assumption|]); rewrite <- E; unfold cutval;
    apply C8_tr12; exact Hs.
Qed.

Lemma fullS_sym23 : forall g, (forall p q r, g p r q = g p q r) ->
  forall x y z t, fullS g x z y t <-> fullS g x y z t.
Proof.
  intros g Hs x y z t. split; intros (a & b & c & Ha & Hb & Hc & E);
    exists a, c, b; do 3 (split; [assumption|]); rewrite <- E; unfold cutval;
    apply C8_tr23; exact Hs.
Qed.

Lemma mirror : forall x a, 1 <= a <= x -> exists a', 1 <= a' <= (x + 1) / 2 /\
  ((a' - 1 = a - 1 /\ x - a' = x - a) \/ (a' - 1 = x - a /\ x - a' = a - 1)).
Proof.
  intros x a Ha. destruct (N.le_gt_cases (2 * a) (x + 1)) as [H | H].
  - exists a. split; [split; [lia | apply N.div_le_lower_bound; lia] | left; auto].
  - exists (x + 1 - a). split; [split; [lia | apply N.div_le_lower_bound; lia] | right; lia].
Qed.

Lemma half_le : forall x, 1 <= x -> (x + 1) / 2 <= x.
Proof. intros x H. apply N.div_le_upper_bound; lia. Qed.

Lemma half_full : forall g x y z t, 1 <= x -> 1 <= y -> 1 <= z ->
  (halfS g x y z t <-> fullS g x y z t).
Proof.
  intros g x y z t Hx Hy Hz. split.
  - intros (a & b & c & Ha & Hb & Hc & E). exists a, b, c.
    pose proof (half_le x Hx). pose proof (half_le y Hy). pose proof (half_le z Hz).
    repeat split; try lia; exact E.
  - intros (a & b & c & Ha & Hb & Hc & E).
    destruct (mirror x a Ha) as (a' & Ha' & HA).
    destruct (mirror y b Hb) as (b' & Hb' & HB).
    destruct (mirror z c Hc) as (c' & Hc' & HC).
    exists a', b', c'. do 3 (split; [assumption|]). rewrite <- E. unfold cutval.
    destruct HA as [[-> ->] | [-> ->]]; destruct HB as [[-> ->] | [-> ->]];
      destruct HC as [[-> ->] | [-> ->]];
      cbn [C8 L8 xorG fold_right Gc]; xbits.
Qed.

Lemma mexprop_ext : forall (S S' : N -> Prop) v v',
  (forall t, S t <-> S' t) -> v = v' -> mexprop S v -> mexprop S' v'.
Proof.
  intros S S' v v' HS -> [H1 H2]. split.
  - rewrite <- HS. exact H1.
  - intros t Ht. apply HS. apply H2. exact Ht.
Qed.

Lemma perm_closure : forall Q : N -> N -> N -> Prop,
  (forall x y z, Q x y z <-> Q y x z) -> (forall x y z, Q x y z <-> Q x z y) ->
  (forall x y z, x <= y -> y <= z -> Q x y z) -> forall x y z, Q x y z.
Proof.
  intros Q H12 H23 Hc x y z.
  destruct (N.le_gt_cases x y); destruct (N.le_gt_cases y z);
    destruct (N.le_gt_cases x z).
  all: first
    [ apply Hc; lia
    | apply H23; apply Hc; lia
    | apply H12; apply Hc; lia
    | apply H12, H23; apply Hc; lia
    | apply H23, H12; apply Hc; lia
    | apply H12, H23, H12; apply Hc; lia ].
Qed.

Lemma canon_to_full : forall M g,
  (forall p q r, g q p r = g p q r) -> (forall p q r, g p r q = g p q r) ->
  (forall x y z, 1 <= x -> x <= y -> y <= z -> z <= M ->
     mexprop (halfS g x y z) (g x y z)) ->
  forall x y z, 1 <= x <= M -> 1 <= y <= M -> 1 <= z <= M ->
     mexprop (fullS g x y z) (g x y z).
Proof.
  intros M g H12 H23 Hc.
  apply (perm_closure (fun x y z => 1 <= x <= M -> 1 <= y <= M -> 1 <= z <= M ->
     mexprop (fullS g x y z) (g x y z))).
  - intros x y z. split; intros H Bx By Bz;
      (eapply mexprop_ext; [ | | apply H; assumption ]);
      [ intro t; apply fullS_sym12; exact H12 | apply H12
      | intro t; symmetry; apply fullS_sym12; exact H12 | symmetry; apply H12 ].
  - intros x y z. split; intros H Bx By Bz;
      (eapply mexprop_ext; [ | | apply H; assumption ]);
      [ intro t; apply fullS_sym23; exact H23 | apply H23
      | intro t; symmetry; apply fullS_sym23; exact H23 | symmetry; apply H23 ].
  - intros x y z Hxy Hyz Bx By Bz.
    eapply mexprop_ext; [ | reflexivity | apply Hc; lia ].
    intro t. apply half_full; lia.
Qed.

End Symmetries.

(* ================================================================== *)
(* Part C. The program                                                *)
(* ================================================================== *)

Open Scope uint63_scope.
Open Scope array_scope.

(* ================================================================== *)
(* Part D. Proofs of the program                                      *)
(* ================================================================== *)

Lemma loop_eq : forall A (f : int -> A -> A) hi i acc H,
  loop f hi i acc H =
  match bdec (i <? hi) with
  | left Hi => loop f hi (i + 1) (f i acc) (Acc_inv H (dec_step hi i Hi))
  | right _ => acc
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma for_spec : forall A (f : int -> A -> A) (lo hi : int) (P : int -> A -> Prop) acc,
  ((φ lo) <= (φ hi))%Z -> P lo acc ->
  (forall i a, ((φ lo) <= (φ i) < (φ hi))%Z -> P i a -> P (i + 1) (f i a)) ->
  P hi (for_ f lo hi acc).
Proof.
  intros A f lo hi P acc Hlh H0 Hs. unfold for_.
  assert (G : forall z i a (H : Acc (Zwf 0) (gap hi i)), gap hi i = z ->
            ((φ lo) <= (φ i) <= (φ hi))%Z -> P i a -> P hi (loop f hi i a H)).
  { intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros i a H Hz Hi Ha. rewrite loop_eq.
    destruct (bdec (i <? hi)) as [E | E].
    - pose proof E as E'. rewrite ltb_spec in E'.
      assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
      eapply IH; [ | reflexivity | lia | apply Hs; [lia | exact Ha] ].
      rewrite <- Hz. apply dec_step. exact E.
    - rewrite <- Bool.not_true_iff_false, ltb_spec in E.
      assert (i = hi) by (apply to_Z_inj; lia). subst. exact Ha. }
  eapply G; [reflexivity | lia | exact H0].
Qed.

Lemma imin_spec : forall a b, (φ (imin a b)) = Z.min (φ a) (φ b).
Proof.
  intros a b. unfold imin. destruct (a <=? b) eqn:E;
    [rewrite leb_spec in E | rewrite <- Bool.not_true_iff_false, leb_spec in E]; lia.
Qed.

Lemma imax_spec : forall a b, (φ (imax a b)) = Z.max (φ a) (φ b).
Proof.
  intros a b. unfold imax. destruct (a <=? b) eqn:E;
    [rewrite leb_spec in E | rewrite <- Bool.not_true_iff_false, leb_spec in E]; lia.
Qed.

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Definition idxZ (d u v w : Z) : Z := ((u * d + v) * d + w)%Z.

Lemma cidx_spec : forall D x y z,
  ((φ D) <= 1000)%Z -> ((φ x) <= 1000)%Z -> ((φ y) <= 1000)%Z -> ((φ z) <= 1000)%Z ->
  (φ (cidx D x y z)) = idxZ (φ D) (φ x) (φ y) (φ z).
Proof.
  intros D x y z HD Hx Hy Hz. unfold cidx, idxZ.
  pose proof (to_Z_bounded D). pose proof (to_Z_bounded x).
  pose proof (to_Z_bounded y). pose proof (to_Z_bounded z).
  assert (E1 : (φ (x * D)) = ((φ x) * (φ D))%Z)
    by (rewrite mul_spec; apply Z.mod_small; rewrite wB_val; nia).
  assert (E2 : (φ (x * D + y)) = ((φ x) * (φ D) + (φ y))%Z)
    by (rewrite add_spec, E1; apply Z.mod_small; rewrite wB_val; nia).
  assert (E3 : (φ ((x * D + y) * D)) = (((φ x) * (φ D) + (φ y)) * (φ D))%Z)
    by (rewrite mul_spec, E2; apply Z.mod_small; rewrite wB_val; nia).
  rewrite add_spec, E3; apply Z.mod_small; rewrite wB_val; nia.
Qed.

Lemma look_sym12 : forall T D x y z, look T D x y z = look T D y x z.
Proof.
  intros T D x y z. unfold look.
  assert (E1 : imin x (imin y z) = imin y (imin x z))
    by (apply to_Z_inj; rewrite !imin_spec; lia).
  assert (E2 : imax x (imax y z) = imax y (imax x z))
    by (apply to_Z_inj; rewrite !imax_spec; lia).
  rewrite E1, E2, (add_comm x y). reflexivity.
Qed.

Lemma look_sym23 : forall T D x y z, look T D x y z = look T D x z y.
Proof.
  intros T D x y z. unfold look.
  assert (E1 : imin y z = imin z y) by (apply to_Z_inj; rewrite !imin_spec; lia).
  assert (E2 : imax y z = imax z y) by (apply to_Z_inj; rewrite !imax_spec; lia).
  assert (E3 : x + y + z = x + z + y)
    by (rewrite <- !add_assoc, (add_comm y z); reflexivity).
  rewrite E1, E2, E3. reflexivity.
Qed.

Notation toN i := (Z.to_N (to_Z i)).
Notation ofN p := (of_Z (Z.of_N p)).

Lemma ofN_toN : forall i : int, ofN (toN i) = i.
Proof.
  intros i. rewrite Z2N.id by (pose proof (to_Z_bounded i); lia). apply of_to_Z.
Qed.

Lemma phi_ofN : forall p : N, (Z.of_N p < wB)%Z -> (φ (ofN p)) = Z.of_N p.
Proof. intros p H. rewrite of_Z_spec. apply Z.mod_small. lia. Qed.

Lemma toN_inj : forall i j : int, toN i = toN j -> i = j.
Proof.
  intros i j H. apply to_Z_inj.
  pose proof (to_Z_bounded i). pose proof (to_Z_bounded j).
  apply (f_equal Z.of_N) in H. rewrite !Z2N.id in H by lia. exact H.
Qed.

Lemma toN_lxor : forall a b, toN (a lxor b) = N.lxor (toN a) (toN b).
Proof.
  intros a b. pose proof (to_Z_bounded a). pose proof (to_Z_bounded b).
  apply N2Z.inj. rewrite N2Z.inj_lxor, lxor_spec', !Z2N.id; try lia.
  apply Z.lxor_nonneg. lia.
Qed.

Lemma toN_sub : forall a b, ((φ b) <= (φ a))%Z -> toN (a - b) = (toN a - toN b)%N.
Proof.
  intros a b H. pose proof (to_Z_bounded a). pose proof (to_Z_bounded b).
  assert (E : (φ (a - b)) = ((φ a) - (φ b))%Z) by sia. rewrite E. lia.
Qed.

Definition gL (T : array int) (D : int) (p q r : N) : N :=
  toN (look T D (ofN p) (ofN q) (ofN r)).

Lemma gL_toN : forall T D x y z, gL T D (toN x) (toN y) (toN z) = toN (look T D x y z).
Proof. intros. unfold gL. rewrite !ofN_toN. reflexivity. Qed.

Lemma gL_sym12 : forall T D p q r, gL T D q p r = gL T D p q r.
Proof. intros. unfold gL. rewrite look_sym12. reflexivity. Qed.

Lemma gL_sym23 : forall T D p q r, gL T D p r q = gL T D p q r.
Proof. intros. unfold gL. rewrite look_sym23. reflexivity. Qed.

Lemma cutv_val : forall T D x y z a b c,
  (1 <= (φ a) <= (φ x))%Z -> (1 <= (φ b) <= (φ y))%Z -> (1 <= (φ c) <= (φ z))%Z ->
  toN (cutv T D x y z a b c)
  = cutval (gL T D) (toN x) (toN y) (toN z) (toN a) (toN b) (toN c).
Proof.
  intros T D x y z a b c Ha Hb Hc. unfold cutv, cutval.
  cbn [C8 L8 xorG fold_right Gc]. rewrite N.lxor_0_r, !toN_lxor.
  change 1%N with (toN 1).
  rewrite <- (toN_sub a 1), <- (toN_sub b 1), <- (toN_sub c 1),
    <- (toN_sub x a), <- (toN_sub y b), <- (toN_sub z c) by (change (φ 1) with 1%Z; lia).
  rewrite !gL_toN. reflexivity.
Qed.

Lemma add_small : forall a b, ((φ a) + (φ b) < wB)%Z -> (φ (a + b)) = ((φ a) + (φ b))%Z.
Proof.
  intros a b H. pose proof (to_Z_bounded a). pose proof (to_Z_bounded b).
  rewrite add_spec. apply Z.mod_small. lia.
Qed.

Lemma sub_small : forall a b, ((φ b) <= (φ a))%Z -> (φ (a - b)) = ((φ a) - (φ b))%Z.
Proof.
  intros a b H. pose proof (to_Z_bounded a). pose proof (to_Z_bounded b).
  rewrite sub_spec. apply Z.mod_small. lia.
Qed.

Lemma look_idx : forall T D x y z (m : Z),
  (φ D) = (m + 1)%Z -> (0 <= m <= 30)%Z ->
  ((φ x) <= m)%Z -> ((φ y) <= m)%Z -> ((φ z) <= m)%Z ->
  exists i, look T D x y z = T.[i] /\
    (φ i) = idxZ (m + 1) (Z.min (φ x) (Z.min (φ y) (φ z)))
            ((φ x) + (φ y) + (φ z) - Z.min (φ x) (Z.min (φ y) (φ z)) - Z.max (φ x) (Z.max (φ y) (φ z)))
            (Z.max (φ x) (Z.max (φ y) (φ z))).
Proof.
  intros T D x y z m HD Hm Hx Hy Hz. unfold look.
  eexists; split; [reflexivity|].
  pose proof (imin_spec y z). pose proof (imin_spec x (imin y z)).
  pose proof (imax_spec y z). pose proof (imax_spec x (imax y z)).
  pose proof (to_Z_bounded x). pose proof (to_Z_bounded y). pose proof (to_Z_bounded z).
  set (lo := imin x (imin y z)) in *. set (hi := imax x (imax y z)) in *.
  clearbody lo hi.
  assert (Hmid : (φ (x + y + z - lo - hi))
     = ((φ x) + (φ y) + (φ z) - Z.min (φ x) (Z.min (φ y) (φ z)) - Z.max (φ x) (Z.max (φ y) (φ z)))%Z).
  { rewrite sub_small, sub_small, add_small, add_small; try lia;
      rewrite ?add_small; try lia. }
  rewrite cidx_spec; try lia.
  rewrite Hmid, HD. f_equal; lia.
Qed.

Lemma gL_idx : forall T D p q r (m : Z),
  (φ D) = (m + 1)%Z -> (0 <= m <= 30)%Z ->
  (Z.of_N p <= m)%Z -> (Z.of_N q <= m)%Z -> (Z.of_N r <= m)%Z ->
  exists i, gL T D p q r = toN T.[i] /\
    (φ i) = idxZ (m + 1) (Z.min (Z.of_N p) (Z.min (Z.of_N q) (Z.of_N r)))
      (Z.of_N p + Z.of_N q + Z.of_N r - Z.min (Z.of_N p) (Z.min (Z.of_N q) (Z.of_N r))
         - Z.max (Z.of_N p) (Z.max (Z.of_N q) (Z.of_N r)))
      (Z.max (Z.of_N p) (Z.max (Z.of_N q) (Z.of_N r))).
Proof.
  intros T D p q r m HD Hm Hp Hq Hr. unfold gL.
  assert (Ep : (φ (ofN p)) = Z.of_N p) by (apply phi_ofN; rewrite wB_val; lia).
  assert (Eq : (φ (ofN q)) = Z.of_N q) by (apply phi_ofN; rewrite wB_val; lia).
  assert (Er : (φ (ofN r)) = Z.of_N r) by (apply phi_ofN; rewrite wB_val; lia).
  destruct (look_idx T D (ofN p) (ofN q) (ofN r) m HD Hm) as (i & E1 & E2); try lia.
  exists i. rewrite E1. split; [reflexivity|]. rewrite E2, Ep, Eq, Er. reflexivity.
Qed.

Lemma lex_lt : forall d u v u' v', (0 < d)%Z -> (0 <= v < d)%Z -> (0 <= v' < d)%Z ->
  ((u * d + v < u' * d + v')%Z <-> (u < u')%Z \/ (u = u' /\ v < v')%Z).
Proof.
  intros d u v u' v' Hd Hv Hv'. split.
  - intros H. destruct (Z.lt_trichotomy u u') as [E | [E | E]].
    + left. exact E.
    + right. subst. lia.
    + exfalso. assert ((u' + 1) * d <= u * d)%Z
        by (apply Z.mul_le_mono_nonneg_r; lia). lia.
  - intros [E | [E1 E2]].
    + assert ((u + 1) * d <= u' * d)%Z by (apply Z.mul_le_mono_nonneg_r; lia). lia.
    + subst. lia.
Qed.

Lemma lex_eq : forall d u v u' v', (0 < d)%Z -> (0 <= v < d)%Z -> (0 <= v' < d)%Z ->
  (u * d + v = u' * d + v')%Z -> u = u' /\ v = v'.
Proof.
  intros d u v u' v' Hd Hv Hv' H.
  destruct (Z.lt_trichotomy u u') as [E | [E | E]].
  - exfalso. assert ((u * d + v < u' * d + v')%Z) by (apply lex_lt; auto). lia.
  - subst. lia.
  - exfalso. assert ((u' * d + v' < u * d + v)%Z) by (apply lex_lt; auto). lia.
Qed.

Lemma idx_lt : forall d a b c a' b' c', (0 < d)%Z ->
  (0 <= b < d)%Z -> (0 <= c < d)%Z -> (0 <= b' < d)%Z -> (0 <= c' < d)%Z ->
  (idxZ d a b c < idxZ d a' b' c')%Z <->
  (a < a')%Z \/ (a = a' /\ ((b < b')%Z \/ (b = b' /\ c < c')%Z)).
Proof.
  intros d a b c a' b' c' Hd Hb Hc Hb' Hc'. unfold idxZ.
  rewrite lex_lt by auto. split.
  - intros [H | [H1 H2]].
    + apply lex_lt in H; auto. destruct H as [H | [H1 H2]]; [left; exact H | right; auto].
    + apply lex_eq in H1; auto. destruct H1 as [-> ->]. right. auto.
  - intros [H | [-> [H | [-> H]]]].
    + left. apply lex_lt; auto.
    + left. apply lex_lt; auto.
    + right. auto.
Qed.

Lemma idx_eq : forall d a b c a' b' c', (0 < d)%Z ->
  (0 <= b < d)%Z -> (0 <= c < d)%Z -> (0 <= b' < d)%Z -> (0 <= c' < d)%Z ->
  idxZ d a b c = idxZ d a' b' c' -> a = a' /\ b = b' /\ c = c'.
Proof.
  intros d a b c a' b' c' Hd Hb Hc Hb' Hc' H. unfold idxZ in H.
  apply lex_eq in H; auto. destruct H as [H ->].
  apply lex_eq in H; auto. destruct H as [-> ->]. auto.
Qed.

Lemma idx_lt_sq : forall d a b c A, (0 < d)%Z -> (0 <= b < d)%Z -> (0 <= c < d)%Z ->
  (a < A)%Z -> (idxZ d a b c < A * d * d)%Z.
Proof.
  intros d a b c A Hd Hb Hc H.
  replace (A * d * d)%Z with (idxZ d A 0 0) by (unfold idxZ; ring).
  apply idx_lt; auto; lia.
Qed.

Lemma idx_ge_sq : forall d a b c, (0 < d)%Z -> (0 <= b)%Z -> (0 <= c)%Z ->
  (a * d * d <= idxZ d a b c)%Z.
Proof. intros. unfold idxZ. nia. Qed.

(* ------------------------------------------------------------------ *)
(* Stamping and mex                                                    *)
(* ------------------------------------------------------------------ *)

Lemma aget_set_same : forall (t : array int) (i : int) (b : int),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same int t i b H). Qed.

Lemma aget_set_other : forall (t : array int) (i j : int) (b : int),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other int t i j b H). Qed.

Lemma alength_set : forall (t : array int) (i : int) (b : int),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set int t i b). Qed.

Lemma aget_oob : forall (t : array int) (i : int),
  (i <? PArray.length t) = false -> t.[i] = PArray.default t.
Proof. intros t i H. exact (get_out_of_bounds int t i H). Qed.

Lemma adefault_set : forall (t : array int) (i : int) (b : int),
  PArray.default t.[i <- b] = PArray.default t.
Proof. intros t i b. exact (default_set int t i b). Qed.

Definition MarkSpec (L st : int) (h : array int -> array int) (R : int -> Prop) : Prop :=
  forall s : array int, PArray.length s = L ->
    PArray.length (h s) = L /\ (forall t, (h s).[t] = s.[t] \/ (h s).[t] = st) /\
    (forall t, ((φ t) < (φ L))%Z -> ((h s).[t] = st <-> s.[t] = st \/ R t)).

Lemma MarkSpec_ext : forall L st h (R R' : int -> Prop),
  (forall t, R t <-> R' t) -> MarkSpec L st h R -> MarkSpec L st h R'.
Proof.
  intros L st h R R' HR H s Hs. destruct (H s Hs) as (H1 & H2 & H3).
  split; [exact H1|]. split; [exact H2|]. intros t Ht. rewrite H3 by exact Ht.
  rewrite HR. tauto.
Qed.

Lemma mark_set : forall L st v, MarkSpec L st (fun s => s.[v <- st]) (fun t => t = v).
Proof.
  intros L st v s Hs. split; [rewrite alength_set; exact Hs|]. split.
  - intros t. destruct (Uint63.eqs v t) as [E | E].
    + subst t. destruct (v <? PArray.length s) eqn:Hb.
      * right. apply aget_set_same. exact Hb.
      * left.
        assert (H1 : (v <? PArray.length (s.[v <- st])) = false)
          by (rewrite alength_set; exact Hb).
        rewrite (aget_oob _ _ H1), (aget_oob _ _ Hb).
        apply adefault_set.
    + left. apply aget_set_other. exact E.
  - intros t Ht. destruct (Uint63.eqs v t) as [E | E].
    + subst t. rewrite aget_set_same by (rewrite Hs, ltb_spec; exact Ht).
      split; [intros _; right; reflexivity | intros _; reflexivity].
    + rewrite aget_set_other by exact E. split; [tauto|].
      intros [H | H]; [exact H | congruence].
Qed.

Lemma mark_for : forall L st (f : int -> array int -> array int) (R : int -> int -> Prop) lo hi,
  ((φ lo) <= (φ hi))%Z ->
  (forall i, ((φ lo) <= (φ i) < (φ hi))%Z -> MarkSpec L st (f i) (R i)) ->
  MarkSpec L st (for_ f lo hi) (fun t => exists i, ((φ lo) <= (φ i) < (φ hi))%Z /\ R i t).
Proof.
  intros L st f R lo hi Hlh Hf s Hs.
  apply (for_spec _ f lo hi (fun i a => PArray.length a = L /\
     (forall t, a.[t] = s.[t] \/ a.[t] = st) /\
     (forall t, ((φ t) < (φ L))%Z -> (a.[t] = st <-> s.[t] = st \/
        exists j, ((φ lo) <= (φ j) < (φ i))%Z /\ R j t)))); [exact Hlh | | ].
  - split; [exact Hs|]. split; [intros t; left; reflexivity|].
    intros t Ht. split; [tauto|]. intros [H | (j & Hj & _)]; [exact H | lia].
  - intros i a Hi (Ha1 & Ha2 & Ha3).
    destruct (Hf i Hi a Ha1) as (H1 & H2 & H3).
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    split; [exact H1|]. split.
    + intros t. destruct (H2 t) as [E | E]; [rewrite E; apply Ha2 | right; exact E].
    + intros t Ht. rewrite H3, Ha3 by exact Ht. rewrite Hi1. split.
      * intros [[E | (j & Hj & Hr)] | Hr]; [left; exact E | right | right].
        -- exists j. split; [lia | exact Hr].
        -- exists i. split; [lia | exact Hr].
      * intros [E | (j & Hj & Hr)]; [left; left; exact E|].
        destruct (Z.eq_dec (φ j) (φ i)) as [Ej | Ej].
        -- right. assert (j = i) by (apply to_Z_inj; exact Ej). subst. exact Hr.
        -- left. right. exists j. split; [lia | exact Hr].
Qed.

Lemma mex_loop_eq : forall s st L t H,
  mex_loop s st L t H =
  match bdec (t <? L) with
  | left Ht =>
      if s.[t] =? st then mex_loop s st L (t + 1) (Acc_inv H (dec_step L t Ht))
      else t
  | right _ => t
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma mex_spec_gen : forall s st L z t H, gap L t = z ->
  ((φ t) <= (φ L))%Z -> (forall u, ((φ u) < (φ t))%Z -> s.[u] = st) ->
  ((φ (mex_loop s st L t H)) <= (φ L))%Z /\
  (forall u, ((φ u) < (φ (mex_loop s st L t H)))%Z -> s.[u] = st) /\
  (((φ (mex_loop s st L t H)) < (φ L))%Z -> s.[mex_loop s st L t H] <> st).
Proof.
  intros s st L z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros t H Hz Ht Hu. rewrite mex_loop_eq.
  destruct (bdec (t <? L)) as [E | E].
  - pose proof E as E'. rewrite ltb_spec in E'.
    destruct (s.[t] =? st) eqn:Es; [apply eqb_spec in Es | apply eqb_false_spec in Es].
    + assert (Ht1 : (φ (t + 1)) = ((φ t) + 1)%Z) by sia.
      apply (IH (gap L (t + 1))); [ rewrite <- Hz; apply dec_step; exact E | reflexivity | lia | ].
      intros u Hu'. destruct (Z.eq_dec (φ u) (φ t)) as [Eu | Eu].
      * assert (u = t) by (apply to_Z_inj; exact Eu). subst u. exact Es.
      * apply Hu. lia.
    + split; [lia|]. split; [exact Hu|]. intros _. exact Es.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in E.
    split; [lia|]. split; [exact Hu|]. intros H'. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Counting: a mex is at most the number of options                    *)
(* ------------------------------------------------------------------ *)

Definition rangeN (n : N) : list N := map N.of_nat (seq 1 (N.to_nat n)).

Lemma In_rangeN : forall a n, (1 <= a <= n)%N -> In a (rangeN n).
Proof.
  intros a n H. unfold rangeN. apply in_map_iff. exists (N.to_nat a).
  split; [apply N2Nat.id|]. apply in_seq. lia.
Qed.

Definition halfvals g (x y z : N) : list N :=
  map (fun '(a, b, c) => cutval g x y z a b c)
    (list_prod (list_prod (rangeN ((x + 1) / 2)) (rangeN ((y + 1) / 2)))
       (rangeN ((z + 1) / 2))).

Lemma halfvals_length : forall g x y z,
  List.length (halfvals g x y z) =
  (N.to_nat ((x + 1) / 2) * N.to_nat ((y + 1) / 2) * N.to_nat ((z + 1) / 2))%nat.
Proof.
  intros. unfold halfvals, rangeN. rewrite length_map, !length_prod, !length_map, !length_seq.
  reflexivity.
Qed.

Lemma halfS_In : forall g x y z t, halfS g x y z t -> In t (halfvals g x y z).
Proof.
  intros g x y z t (a & b & c & Ha & Hb & Hc & E). unfold halfvals.
  apply in_map_iff. exists (a, b, c). split; [exact E|].
  apply in_prod; [apply in_prod|]; apply In_rangeN; assumption.
Qed.

Lemma count_bound : forall (S : N -> Prop) (l : list N) n,
  (forall u, (u < n)%N -> S u) -> (forall u, S u -> In u l) ->
  (N.to_nat n <= List.length l)%nat.
Proof.
  intros S l n H1 H2.
  rewrite <- (length_seq (N.to_nat n) 0), <- (length_map N.to_nat l).
  apply NoDup_incl_length; [apply seq_NoDup|].
  intros j Hj. apply in_seq in Hj.
  rewrite <- (Nat2N.id j). apply in_map. apply H2. apply H1. lia.
Qed.

Lemma mark_a_spec : forall T D x y z ha hb hc st L,
  ((φ ha) <= 1000)%Z -> ((φ hb) <= 1000)%Z -> ((φ hc) <= 1000)%Z ->
  MarkSpec L st (mark_a T D x y z ha hb hc st)
    (fun t => exists a b c, (1 <= (φ a) <= (φ ha))%Z /\ (1 <= (φ b) <= (φ hb))%Z /\
       (1 <= (φ c) <= (φ hc))%Z /\ t = cutv T D x y z a b c).
Proof.
  intros T D x y z ha hb hc st L Ha Hb Hc.
  pose proof (to_Z_bounded ha) as B1. pose proof (to_Z_bounded hb) as B2.
  pose proof (to_Z_bounded hc) as B3.
  assert (Ea : (φ (ha + 1)) = ((φ ha) + 1)%Z) by (apply add_small; rewrite wB_val; change (φ 1) with 1%Z; lia).
  assert (Eb : (φ (hb + 1)) = ((φ hb) + 1)%Z) by (apply add_small; rewrite wB_val; change (φ 1) with 1%Z; lia).
  assert (Ec : (φ (hc + 1)) = ((φ hc) + 1)%Z) by (apply add_small; rewrite wB_val; change (φ 1) with 1%Z; lia).
  assert (H : MarkSpec L st (mark_a T D x y z ha hb hc st)
    (fun t => exists a, ((φ 1) <= (φ a) < (φ (ha + 1)))%Z /\
       exists b, ((φ 1) <= (φ b) < (φ (hb + 1)))%Z /\
       exists c, ((φ 1) <= (φ c) < (φ (hc + 1)))%Z /\ t = cutv T D x y z a b c)).
  { unfold mark_a. apply mark_for; [change (φ 1) with 1%Z; lia|].
    intros a _. unfold mark_b. apply mark_for; [change (φ 1) with 1%Z; lia|].
    intros b _. unfold mark_c. apply mark_for; [change (φ 1) with 1%Z; lia|].
    intros c _. apply mark_set. }
  eapply MarkSpec_ext; [| exact H].
  intros t. change (φ 1) with 1%Z. rewrite Ea, Eb, Ec. split.
  - intros (a & Ha' & b & Hb' & c & Hc' & E). exists a, b, c. repeat split; try lia; exact E.
  - intros (a & b & c & Ha' & Hb' & Hc' & E). exists a. split; [lia|].
    exists b. split; [lia|]. exists c. split; [lia | exact E].
Qed.

(* ------------------------------------------------------------------ *)
(* The table                                                          *)
(* ------------------------------------------------------------------ *)

Lemma succ_small : forall i hi, ((φ i) < (φ hi))%Z -> ((φ hi) <= 1000)%Z -> (φ (i + 1)) = ((φ i) + 1)%Z.
Proof.
  intros i hi H1 H2. pose proof (to_Z_bounded i).
  apply add_small. rewrite wB_val. change (φ 1) with 1%Z. lia.
Qed.

Lemma alength_make : forall (n : int) (b : int),
  PArray.length (PArray.make n b)
  = if n <=? PArray.max_length then n else PArray.max_length.
Proof. intros n b. exact (length_make int n b). Qed.

Lemma aget_make : forall (n i : int) (b : int), (PArray.make n b).[i] = b.
Proof. intros n i b. exact (get_make int b n i). Qed.

Section Table.
Variables (D L : int) (m : Z).
Hypothesis HD : (φ D) = (m + 1)%Z.
Hypothesis Hm : (0 <= m <= 30)%Z.
Hypothesis HL : (φ L) = ((m + 1) * (m + 1) * (m + 1))%Z.

Definition Z0 (T : array int) : Prop :=
  forall i, ((φ i) < (m + 1) * (m + 1))%Z -> T.[i] = 0.

Definition AgB (T T' : array int) (K : Z) : Prop :=
  forall i, ((φ i) < K)%Z -> T.[i] = T'.[i].

Definition idxN (X Y W : N) : Z := idxZ (m + 1) (Z.of_N X) (Z.of_N Y) (Z.of_N W).

Definition Good (T : array int) (k : Z) : Prop :=
  forall X Y W : N, (1 <= X)%N -> (X <= Y)%N -> (Y <= W)%N -> (Z.of_N W <= m)%Z ->
    (idxN X Y W < k)%Z -> mexprop (halfS (gL T D) X Y W) (gL T D X Y W).

Lemma AgB_weaken : forall T T' K K', AgB T T' K -> (K' <= K)%Z -> AgB T T' K'.
Proof. intros T T' K K' H HK i Hi. apply H. lia. Qed.

Lemma gL_zero : forall T p q r, Z0 T ->
  (Z.of_N p <= m)%Z -> (Z.of_N q <= m)%Z -> (Z.of_N r <= m)%Z ->
  (p = 0 \/ q = 0 \/ r = 0)%N -> gL T D p q r = 0%N.
Proof.
  intros T p q r H0 Hp Hq Hr Hz.
  destruct (gL_idx T D p q r m HD Hm Hp Hq Hr) as (i & E1 & E2).
  rewrite E1, H0; [reflexivity|]. rewrite E2.
  replace ((m + 1) * (m + 1))%Z with (1 * (m + 1) * (m + 1))%Z by ring.
  apply idx_lt_sq; lia.
Qed.

Lemma gL_frame_lt : forall T T' (A : Z) p q r, AgB T T' (A * (m + 1) * (m + 1)) ->
  (Z.of_N p <= m)%Z -> (Z.of_N q <= m)%Z -> (Z.of_N r <= m)%Z ->
  (Z.of_N p < A)%Z -> gL T D p q r = gL T' D p q r.
Proof.
  intros T T' A p q r HA Hp Hq Hr HpA.
  destruct (gL_idx T D p q r m HD Hm Hp Hq Hr) as (i & E1 & E2).
  destruct (gL_idx T' D p q r m HD Hm Hp Hq Hr) as (i' & E1' & E2').
  assert (i' = i) by (apply to_Z_inj; lia). subst i'.
  rewrite E1, E1', HA; [reflexivity|]. rewrite E2. apply idx_lt_sq; lia.
Qed.

Lemma gL_canon : forall T X Y W, (X <= Y)%N -> (Y <= W)%N -> (Z.of_N W <= m)%Z ->
  exists i, gL T D X Y W = toN T.[i] /\ (φ i) = idxN X Y W.
Proof.
  intros T X Y W H1 H2 H3.
  destruct (gL_idx T D X Y W m HD Hm) as (i & E1 & E2); try lia.
  exists i. split; [exact E1|]. rewrite E2. unfold idxN. f_equal; lia.
Qed.

Lemma gL_frame_canon : forall T T' K X Y W, AgB T T' K ->
  (X <= Y)%N -> (Y <= W)%N -> (Z.of_N W <= m)%Z -> (idxN X Y W < K)%Z ->
  gL T D X Y W = gL T' D X Y W.
Proof.
  intros T T' K X Y W HA H1 H2 H3 HK.
  destruct (gL_canon T X Y W H1 H2 H3) as (i & E1 & E2).
  destruct (gL_canon T' X Y W H1 H2 H3) as (i' & E1' & E2').
  assert (i' = i) by (apply to_Z_inj; lia). subst i'.
  rewrite E1, E1', HA; [reflexivity | lia].
Qed.

Lemma halfS_frame : forall T T' X Y W t,
  AgB T T' (Z.of_N X * (m + 1) * (m + 1)) ->
  (1 <= X)%N -> (1 <= Y)%N -> (1 <= W)%N ->
  (Z.of_N X <= m)%Z -> (Z.of_N Y <= m)%Z -> (Z.of_N W <= m)%Z ->
  (halfS (gL T D) X Y W t <-> halfS (gL T' D) X Y W t).
Proof.
  intros T T' X Y W t HA H1 H2 H3 B1 B2 B3.
  pose proof (half_le X H1). pose proof (half_le Y H2). pose proof (half_le W H3).
  assert (Hc : forall a b c, (1 <= a <= (X + 1) / 2)%N -> (1 <= b <= (Y + 1) / 2)%N ->
             (1 <= c <= (W + 1) / 2)%N ->
             cutval (gL T D) X Y W a b c = cutval (gL T' D) X Y W a b c).
  { intros a b c Ha Hb Hc. unfold cutval. apply C8_ext.
    intros p q r Hp Hq Hr. apply (gL_frame_lt T T' (Z.of_N X)); [exact HA | lia..]. }
  split; intros (a & b & c & Ha & Hb & Hc' & E); exists a, b, c;
    (do 3 (split; [assumption|])); rewrite <- E; [symmetry|]; apply Hc; assumption.
Qed.

Lemma R_half : forall T x y z t,
  (1 <= (φ x) <= m)%Z -> (1 <= (φ y) <= m)%Z -> (1 <= (φ z) <= m)%Z ->
  (exists a b c, (1 <= (φ a) <= (φ ((x + 1) / 2)))%Z /\ (1 <= (φ b) <= (φ ((y + 1) / 2)))%Z /\
       (1 <= (φ c) <= (φ ((z + 1) / 2)))%Z /\ t = cutv T D x y z a b c)
  <-> halfS (gL T D) (toN x) (toN y) (toN z) (toN t).
Proof.
  intros T x y z t Hx Hy Hz.
  assert (Hh : forall u, (1 <= (φ u) <= m)%Z -> (φ ((u + 1) / 2)) = (((φ u) + 1) / 2)%Z).
  { intros u Hu. rewrite div_spec, add_small by (rewrite wB_val; change (φ 1) with 1%Z; lia).
    reflexivity. }
  rewrite (Hh x Hx), (Hh y Hy), (Hh z Hz). change (φ 1) with 1%Z.
  split.
  - intros (a & b & c & Ha & Hb & Hc & E). exists (toN a), (toN b), (toN c).
    rewrite E, cutv_val by sia. repeat split; try sia; reflexivity.
  - intros (a & b & c & Ha & Hb & Hc & E).
    assert (Ea : (φ (ofN a)) = Z.of_N a) by (apply phi_ofN; rewrite wB_val; sia).
    assert (Eb : (φ (ofN b)) = Z.of_N b) by (apply phi_ofN; rewrite wB_val; sia).
    assert (Ec : (φ (ofN c)) = Z.of_N c) by (apply phi_ofN; rewrite wB_val; sia).
    exists (ofN a), (ofN b), (ofN c). rewrite Ea, Eb, Ec.
    repeat split; try sia.
    apply toN_inj. rewrite cutv_val by sia. rewrite Ea, Eb, Ec, !N2Z.id. symmetry. exact E.
Qed.

Definition Inv (T seen : array int) (k : Z) : Prop :=
  PArray.length T = L /\ PArray.length seen = L /\ Z0 T /\
  (forall t, ((φ (seen.[t])) <= k)%Z) /\ Good T k /\ (0 <= k)%Z.

Lemma cell_spec : forall T seen x y z,
  (1 <= (φ x))%Z -> ((φ x) <= (φ y))%Z -> ((φ y) <= (φ z))%Z -> ((φ z) <= m)%Z ->
  Inv T seen (idxZ (m + 1) (φ x) (φ y) (φ z)) ->
  Inv (fst (cell D L x y z (T, seen))) (snd (cell D L x y z (T, seen)))
      (idxZ (m + 1) (φ x) (φ y) (φ z) + 1).
Proof.
  intros T seen x y z Hx Hxy Hyz Hz (HlT & Hls & HZ0 & Hst & HG & Hk0).
  set (k := idxZ (m + 1) (φ x) (φ y) (φ z)) in *.
  assert (Hkb : (k < (m + 1) * (m + 1) * (m + 1))%Z) by (apply idx_lt_sq; lia).
  assert (Hkl : ((m + 1) * (m + 1) <= k)%Z).
  { pose proof (idx_ge_sq (m + 1) (φ x) (φ y) (φ z) ltac:(lia) ltac:(lia) ltac:(lia)) as G1.
    assert (G2 : (1 * ((m + 1) * (m + 1)) <= (φ x) * ((m + 1) * (m + 1)))%Z)
      by (apply Z.mul_le_mono_nonneg_r; lia).
    rewrite Z.mul_assoc in G2. lia. }
  assert (Hck : (φ (cidx D x y z)) = k) by (rewrite cidx_spec, HD by lia; reflexivity).
  assert (Hst1 : (φ (cidx D x y z + 1)) = (k + 1)%Z)
    by (rewrite add_small, Hck; [reflexivity | rewrite Hck, wB_val; change (φ 1) with 1%Z; lia]).
  unfold cell. cbv beta iota zeta. cbn [fst snd].
  set (stamp := cidx D x y z + 1) in *.
  set (X := toN x). set (Y := toN y). set (W := toN z).
  assert (EX : Z.of_N X = (φ x)) by (unfold X; lia).
  assert (EY : Z.of_N Y = (φ y)) by (unfold Y; lia).
  assert (EW : Z.of_N W = (φ z)) by (unfold W; lia).
  assert (Hha : ((φ ((x + 1) / 2)) <= 1000)%Z)
    by (rewrite div_spec, add_small by (rewrite wB_val; change (φ 1) with 1%Z; lia);
        change (φ 1) with 1%Z; change (φ 2) with 2%Z; apply Z.div_le_upper_bound; lia).
  assert (Hhb : ((φ ((y + 1) / 2)) <= 1000)%Z)
    by (rewrite div_spec, add_small by (rewrite wB_val; change (φ 1) with 1%Z; lia);
        change (φ 1) with 1%Z; change (φ 2) with 2%Z; apply Z.div_le_upper_bound; lia).
  assert (Hhc : ((φ ((z + 1) / 2)) <= 1000)%Z)
    by (rewrite div_spec, add_small by (rewrite wB_val; change (φ 1) with 1%Z; lia);
        change (φ 1) with 1%Z; change (φ 2) with 2%Z; apply Z.div_le_upper_bound; lia).
  destruct (mark_a_spec T D x y z ((x + 1) / 2) ((y + 1) / 2) ((z + 1) / 2) stamp L
              Hha Hhb Hhc seen Hls) as (Hl1 & Hf1 & Hi1).
  set (seen1 := mark_a T D x y z ((x + 1) / 2) ((y + 1) / 2) ((z + 1) / 2) stamp seen) in *.
  assert (Hkey : forall t, ((φ t) < (φ L))%Z ->
            (seen1.[t] = stamp <-> halfS (gL T D) X Y W (toN t))).
  { intros t Ht. rewrite Hi1 by exact Ht.
    unfold X, Y, W. rewrite <- R_half by lia. split.
    - intros [E | E]; [| exact E]. exfalso. pose proof (Hst t) as B.
      rewrite E, Hst1 in B. lia.
    - intros E. right. exact E. }
  pose proof (mex_spec_gen seen1 stamp L _ 0 (Zwf_well_founded 0 (gap L 0)) eq_refl)
    as (Hm1 & Hm2 & Hm3); [pose proof (to_Z_bounded L); change (φ 0) with 0%Z; lia
                          | intros u Hu; pose proof (to_Z_bounded u); change (φ 0) with 0%Z in Hu; lia |].
  set (mm := mex_loop seen1 stamp L 0 (Zwf_well_founded 0 (gap L 0))) in *.
  assert (HU : forall U : N, (Z.of_N U < (φ mm))%Z -> halfS (gL T D) X Y W U).
  { intros U HUm. assert (Eu : (φ (ofN U)) = Z.of_N U) by (apply phi_ofN; rewrite wB_val; lia).
    replace U with (toN (ofN U)) by (rewrite Eu; apply N2Z.id).
    apply Hkey; [lia|]. apply Hm2. lia. }
  assert (Hmlt : ((φ mm) < (φ L))%Z).
  { destruct (Z.lt_ge_cases (φ mm) (φ L)) as [H | H]; [exact H|]. exfalso.
    assert (Hc := count_bound (halfS (gL T D) X Y W) (halfvals (gL T D) X Y W) (toN L)
                   (fun U HUL => HU U ltac:(lia)) (halfS_In _ _ _ _)).
    rewrite halfvals_length in Hc.
    pose proof (half_le X ltac:(lia)). pose proof (half_le Y ltac:(lia)).
    pose proof (half_le W ltac:(lia)).
    apply Nat2Z.inj_le in Hc. rewrite !Nat2Z.inj_mul, !N_nat_Z, Z2N.id in Hc
      by (pose proof (to_Z_bounded L); lia).
    rewrite HL in Hc.
    assert (Ba : (0 <= Z.of_N ((X + 1) / 2) <= m)%Z) by lia.
    assert (Bb : (0 <= Z.of_N ((Y + 1) / 2) <= m)%Z) by lia.
    assert (Bc : (0 <= Z.of_N ((W + 1) / 2) <= m)%Z) by lia.
    set (a := Z.of_N ((X + 1) / 2)) in *. set (b := Z.of_N ((Y + 1) / 2)) in *.
    set (c := Z.of_N ((W + 1) / 2)) in *.
    assert (P1 : (a * b * c <= m * m * m)%Z)
      by (apply Z.mul_le_mono_nonneg; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia | lia | lia]).
    assert (P2 : (m * m * m < (m + 1) * (m + 1) * (m + 1))%Z) by (clear - Hm; nia).
    lia. }
  assert (Hmex : mexprop (halfS (gL T D) X Y W) (toN mm)).
  { split.
    - intros H. apply (Hm3 Hmlt). apply Hkey; [exact Hmlt | exact H].
    - intros U HUm. apply HU. lia. }
  assert (HA : AgB T (T.[cidx D x y z <- mm]) k).
  { intros i Hi. rewrite aget_set_other; [reflexivity|]. intro E. rewrite <- E in Hi. lia. }
  split; [rewrite alength_set; exact HlT|].
  split; [exact Hl1|].
  split.
  { intros i Hi. rewrite aget_set_other; [apply HZ0; exact Hi|].
    intro E. rewrite E in Hck. lia. }
  split.
  { intros t. destruct (Hf1 t) as [E | E]; rewrite E; [pose proof (Hst t); lia | lia]. }
  split; [| lia].
  intros X' Y' W' H1 H2 H3 H4 Hidx.
  assert (B1 : (Z.of_N X' * (m + 1) * (m + 1) <= idxN X' Y' W')%Z)
    by (apply idx_ge_sq; lia).
  destruct (Z.lt_ge_cases (idxN X' Y' W') k) as [Hlt | Hge].
  - pose proof (HG X' Y' W' H1 H2 H3 H4 Hlt) as HG'.
    eapply mexprop_ext; [ | | exact HG' ].
    + intro t. apply halfS_frame; [eapply AgB_weaken; [exact HA | lia] | lia..].
    + apply (gL_frame_canon _ _ k); assumption.
  - assert (Eq : idxN X' Y' W' = k) by lia.
    unfold idxN, k in Eq.
    apply idx_eq in Eq; [| lia..]. destruct Eq as (E1 & E2 & E3).
    assert (X' = X) by lia. assert (Y' = Y) by lia. assert (W' = W) by lia. subst X' Y' W'.
    eapply mexprop_ext; [ | | exact Hmex ].
    + intro t. apply halfS_frame; [eapply AgB_weaken; [exact HA | lia] | lia..].
    + destruct (gL_canon (T.[cidx D x y z <- mm]) X Y W) as (i & Ei & Hi); try lia.
      assert (i = cidx D x y z) by (apply to_Z_inj; rewrite Hi, Hck; unfold idxN, k in *; lia).
      subst i. rewrite Ei, aget_set_same; [reflexivity|].
      rewrite HlT, ltb_spec, Hck, HL. lia.
Qed.

Lemma Inv_ext : forall T s k k', Inv T s k -> (k <= k')%Z ->
  (forall X Y W, (1 <= X)%N -> (X <= Y)%N -> (Y <= W)%N -> (Z.of_N W <= m)%Z ->
     (k <= idxN X Y W)%Z -> (idxN X Y W < k')%Z -> False) ->
  Inv T s k'.
Proof.
  intros T s k k' (H1 & H2 & H3 & H4 & H5 & H6) Hk Hn.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [intros t; pose proof (H4 t); lia|]. split; [|lia].
  intros X Y W B1 B2 B3 B4 B5. apply H5; try assumption.
  destruct (Z.lt_ge_cases (idxN X Y W) k) as [E | E]; [exact E|].
  exfalso. exact (Hn X Y W B1 B2 B3 B4 E B5).
Qed.

Lemma table_spec :
  Inv (fst (table D L)) (snd (table D L)) (idxZ (m + 1) (m + 1) 0 0).
Proof.
  assert (Hd : (0 < m + 1)%Z) by lia.
  unfold table.
  replace (idxZ (m + 1) (m + 1) 0 0) with (idxZ (m + 1) (φ D) 0 0) by (rewrite HD; reflexivity).
  apply (for_spec _ _ 1 D (fun x st => Inv (fst st) (snd st) (idxZ (m + 1) (φ x) 0 0)));
    change (φ 1) with 1%Z; [lia | |].
  - assert (HmL : PArray.length (PArray.make L 0) = L).
    { rewrite alength_make.
      replace (L <=? PArray.max_length) with true; [reflexivity|].
      symmetry. rewrite leb_spec, HL. change (φ PArray.max_length) with 4194303%Z. nia. }
    cbn [fst snd]. split; [exact HmL|]. split; [exact HmL|].
    split; [intros i _; apply aget_make|].
    split; [intros t; rewrite aget_make; change (φ 0) with 0%Z; unfold idxZ; nia|].
    split; [|unfold idxZ; nia].
    intros X Y W B1 B2 B3 B4 B5. exfalso.
    unfold idxN in B5. apply idx_lt in B5; lia.
  - intros x st Hx Inv0.
    rewrite (succ_small x D) by lia.
    replace (idxZ (m + 1) ((φ x) + 1) 0 0) with (idxZ (m + 1) (φ x) (φ D) 0)
      by (rewrite HD; unfold idxZ; ring).
    apply (for_spec _ _ x D (fun y st => Inv (fst st) (snd st) (idxZ (m + 1) (φ x) (φ y) 0)));
      [lia | |].
    + apply (Inv_ext _ _ _ _ Inv0); [unfold idxZ; nia|].
      intros X Y W B1 B2 B3 B4 B5 B6. unfold idxN in B5, B6.
      apply Z.le_ngt in B5. rewrite idx_lt in B5, B6 by lia. lia.
    + intros y st' Hy Inv1.
      rewrite (succ_small y D) by lia.
      replace (idxZ (m + 1) (φ x) ((φ y) + 1) 0) with (idxZ (m + 1) (φ x) (φ y) (φ D))
        by (rewrite HD; unfold idxZ; ring).
      apply (for_spec _ _ y D (fun z st => Inv (fst st) (snd st) (idxZ (m + 1) (φ x) (φ y) (φ z))));
        [lia | |].
      * apply (Inv_ext _ _ _ _ Inv1); [unfold idxZ; nia|].
        intros X Y W B1 B2 B3 B4 B5 B6. unfold idxN in B5, B6.
        apply Z.le_ngt in B5. rewrite idx_lt in B5, B6 by lia. lia.
      * intros z [T seen] Hz Inv2.
        rewrite (succ_small z D) by lia.
        replace (idxZ (m + 1) (φ x) (φ y) ((φ z) + 1)) with (idxZ (m + 1) (φ x) (φ y) (φ z) + 1)%Z
          by (unfold idxZ; ring).
        apply cell_spec; try lia. exact Inv2.
Qed.

End Table.

(* ------------------------------------------------------------------ *)
(* The input and the final fold                                       *)
(* ------------------------------------------------------------------ *)

Lemma repr_nth : forall (a : array uint) (xs : list N), repr a xs ->
  forall j : int, ((φ j) < Z.of_nat (List.length xs))%Z ->
  nth_error xs (Z.to_nat (φ j)) = Some (toN (a.[j])).
Proof.
  intros a xs [Hl Hc] j Hj.
  destruct (Hc (Z.to_nat (φ j)) ltac:(lia)) as (v & Hv & Hr).
  unfold repr, repr_uint in Hr.
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded j); lia).
  rewrite of_to_Z in Hr. rewrite Hv. f_equal. symmetry. exact Hr.
Qed.

Lemma repr_len : forall (a : array uint) (xs : list N), repr a xs ->
  (φ (PArray.length a)) = Z.of_nat (List.length xs).
Proof. intros a xs [Hl _]. symmetry. exact Hl. Qed.

Lemma Forall_nth : forall A (P : A -> Prop) l k v,
  Forall P l -> nth_error l k = Some v -> P v.
Proof.
  intros A P l k v H E. rewrite Forall_forall in H. apply H.
  eapply nth_error_In. exact E.
Qed.

Lemma nth_error_combine_some : forall A B (l : list A) (l' : list B) k x y,
  nth_error l k = Some x -> nth_error l' k = Some y ->
  nth_error (combine l l') k = Some (x, y).
Proof.
  intros A B l. induction l as [|u l IH]; intros l' k x y H1 H2.
  - destruct k; discriminate.
  - destruct l' as [|u' l']; [destruct k; discriminate|].
    destruct k as [|k]; simpl in *.
    + injection H1 as ->. injection H2 as ->. reflexivity.
    + apply IH; assumption.
Qed.

Lemma nth_error_combine_inv : forall A B (l : list A) (l' : list B) k x y,
  nth_error (combine l l') k = Some (x, y) ->
  nth_error l k = Some x /\ nth_error l' k = Some y.
Proof.
  intros A B l. induction l as [|u l IH]; intros l' k x y H.
  - destruct k; discriminate.
  - destruct l' as [|u' l']; [destruct k; discriminate|].
    destruct k as [|k]; simpl in *.
    + injection H as -> ->. auto.
    + apply IH; assumption.
Qed.

Lemma firstn_S_nth : forall A (l : list A) k v,
  nth_error l k = Some v -> firstn (S k) l = firstn k l ++ [v].
Proof.
  intros A l. induction l as [|u l IH]; intros k v H.
  - destruct k; discriminate.
  - destruct k as [|k]; simpl in *.
    + injection H as ->. reflexivity.
    + rewrite (IH k v H). reflexivity.
Qed.

Lemma nth_error_lt : forall A (l : list A) k v, nth_error l k = Some v ->
  (k < List.length l)%nat.
Proof. intros A l k v H. apply nth_error_Some. rewrite H. discriminate. Qed.

Lemma some_inj : forall A (o : option A) u v, o = Some u -> o = Some v -> u = v.
Proof. intros A o u v H1 H2. rewrite H1 in H2. injection H2 as ->. reflexivity. Qed.

Lemma opponent_neq : forall s, opponent s <> s.
Proof. intros []; discriminate. Qed.

Lemma winner_impl_correct :
  forall (s : player) (xs ys zs : list N) (s' : player) (a b c : array uint),
  valid_input xs ys zs -> repr s' s -> repr a xs -> repr b ys -> repr c zs ->
  exists o : player, repr (winner_impl s' a b c) o /\ winner_spec s xs ys zs o.
Proof.
  intros s xs ys zs s' a b c Hv Hs Ha Hb Hc.
  unfold repr, repr_player in Hs. subst s'.
  destruct Hv as [Hn Hyl Hzl Fx Fy Fz]. unfold len in Hn, Hyl, Hzl.
  pose proof (repr_len a xs Ha) as La. pose proof (repr_len b ys Hb) as Lb.
  pose proof (repr_len c zs Hc) as Lc.
  (* every side, read at an index of the input *)
  assert (Side : forall j : int, ((φ j) < Z.of_nat (List.length xs))%Z ->
     (1 <= (φ (PArray.get@{Set} a j)) <= 30 /\ 1 <= (φ (PArray.get@{Set} b j)) <= 30 /\
      1 <= (φ (PArray.get@{Set} c j)) <= 30)%Z /\
     nth_error (initial xs ys zs) (Z.to_nat (φ j)) =
       Some (toN (PArray.get@{Set} a j), toN (PArray.get@{Set} b j),
             toN (PArray.get@{Set} c j))).
  { intros j Hj.
    assert (E1 := repr_nth a xs Ha j ltac:(lia)).
    assert (E2 := repr_nth b ys Hb j ltac:(lia)).
    assert (E3 := repr_nth c zs Hc j ltac:(lia)).
    pose proof (Forall_nth _ _ _ _ _ Fx E1). pose proof (Forall_nth _ _ _ _ _ Fy E2).
    pose proof (Forall_nth _ _ _ _ _ Fz E3). cbv beta in *.
    change (@PArray.get@{repr_array.u0} uint a j) with (@PArray.get@{Set} uint a j) in *.
    change (@PArray.get@{repr_array.u0} uint b j) with (@PArray.get@{Set} uint b j) in *.
    change (@PArray.get@{repr_array.u0} uint c j) with (@PArray.get@{Set} uint c j) in *.
    pose proof (to_Z_bounded (a.[j])). pose proof (to_Z_bounded (b.[j])).
    pose proof (to_Z_bounded (c.[j])).
    split; [lia|]. unfold initial.
    apply nth_error_combine_some; [apply nth_error_combine_some|]; assumption. }
  unfold winner_impl.
  set (n := PArray.length a).
  assert (Hna : (φ n) = Z.of_nat (List.length xs)) by exact La.
  set (Mx := for_ (fun i m => imax m (imax a.[i] (imax b.[i] c.[i]))) 0 n 0).
  assert (HM : (0 <= (φ Mx) <= 30)%Z /\ forall j, ((φ j) < (φ n))%Z ->
     ((φ (PArray.get@{Set} a j)) <= (φ Mx) /\ (φ (PArray.get@{Set} b j)) <= (φ Mx) /\
      (φ (PArray.get@{Set} c j)) <= (φ Mx))%Z).
  { unfold Mx.
    apply (for_spec _ _ 0 n (fun i mm => (0 <= (φ mm) <= 30)%Z /\ forall j, ((φ j) < (φ i))%Z ->
     ((φ (PArray.get@{Set} a j)) <= (φ mm) /\ (φ (PArray.get@{Set} b j)) <= (φ mm) /\
      (φ (PArray.get@{Set} c j)) <= (φ mm))%Z));
      change (φ 0) with 0%Z.
    - pose proof (to_Z_bounded n). lia.
    - split; [lia|]. intros j Hj. pose proof (to_Z_bounded j). lia.
    - intros i mm Hi [H1 H2].
      destruct (Side i ltac:(lia)) as [Bi _].
      rewrite (succ_small i n) by lia.
      rewrite !imax_spec. split; [lia|].
      intros j Hj. destruct (Z.eq_dec (φ j) (φ i)) as [E | E].
      + assert (j = i) by (apply to_Z_inj; exact E). subst j. lia.
      + specialize (H2 j ltac:(lia)). lia. }
  destruct HM as [HMb HMs].
  set (mval := (φ Mx)) in *.
  assert (HD : (φ (Mx + 1)) = (mval + 1)%Z)
    by (apply add_small; rewrite wB_val; change (φ 1) with 1%Z; lia).
  assert (HL : (φ ((Mx + 1) * (Mx + 1) * (Mx + 1))) = ((mval + 1) * (mval + 1) * (mval + 1))%Z).
  { assert (E1 : (φ ((Mx + 1) * (Mx + 1))) = ((mval + 1) * (mval + 1))%Z)
      by (rewrite mul_spec, HD; apply Z.mod_small; rewrite wB_val; nia).
    rewrite mul_spec, E1, HD. apply Z.mod_small. rewrite wB_val. nia. }
  set (D := Mx + 1) in *. set (L := D * D * D) in *.
  destruct (table_spec D L mval HD ltac:(lia) HL) as (HlT & _ & HZ0 & _ & HG & _).
  set (T := fst (table D L)) in *.
  set (g := gL T D).
  set (Mn := Z.to_N mval).
  assert (Hg0 : forall x y z, (x <= Mn)%N -> (y <= Mn)%N -> (z <= Mn)%N ->
            (x = 0 \/ y = 0 \/ z = 0)%N -> g x y z = 0%N).
  { intros x y z Bx By Bz H. apply (gL_zero D L mval HD ltac:(lia) T); try lia; assumption. }
  assert (Hmex : forall x y z, (1 <= x <= Mn)%N -> (1 <= y <= Mn)%N -> (1 <= z <= Mn)%N ->
            mexprop (fullS g x y z) (g x y z)).
  { apply canon_to_full; [apply gL_sym12 | apply gL_sym23 |].
    intros x y z B1 B2 B3 B4. apply HG; try lia.
    unfold idxN. apply idx_lt; lia. }
  assert (Hj : forall k, (k < List.length xs)%nat ->
     exists j : int, (φ j) = Z.of_nat k /\ Z.to_nat (φ j) = k /\ ((φ j) < (φ n))%Z).
  { intros k Hk. exists (of_Z (Z.of_nat k)).
    assert (E : (φ (of_Z (Z.of_nat k))) = Z.of_nat k)
      by (rewrite of_Z_spec; apply Z.mod_small; rewrite wB_val; lia).
    rewrite E. lia. }
  assert (Hlen : List.length (initial xs ys zs) = List.length xs).
  { unfold initial.
    assert (C1 : forall (l : list (N * N)) (l' : list N),
               List.length (combine l l') = Nat.min (List.length l) (List.length l'))
      by (intros; apply length_combine).
    assert (C2 : forall (l : list N) (l' : list N),
               List.length (combine l l') = Nat.min (List.length l) (List.length l'))
      by (intros; apply length_combine).
    rewrite C1, C2. lia. }
  assert (Hbd : bounded Mn (initial xs ys zs)).
  { intros x y z Hin. apply In_nth_error in Hin as (k & Hk).
    assert (Hkl : (k < List.length xs)%nat).
    { rewrite <- Hlen. exact (nth_error_lt _ _ _ _ Hk). }
    destruct (Hj k Hkl) as (j & E1 & E2 & E3).
    destruct (Side j ltac:(lia)) as [Bs Hn'].
    rewrite E2 in Hn'. pose proof (some_inj _ _ _ _ Hk Hn') as Ex.
    injection Ex as -> -> ->.
    pose proof (HMs j E3). unfold Mn. lia. }
  set (gx := for_ (fun i acc => acc lxor look T D a.[i] b.[i] c.[i]) 0 n 0).
  assert (Hgx : toN gx = xorG g (initial xs ys zs)).
  { assert (H : toN gx = xorG g (firstn (Z.to_nat (φ n)) (initial xs ys zs))).
    { unfold gx.
      apply (for_spec _ _ 0 n (fun i acc =>
               toN acc = xorG g (firstn (Z.to_nat (φ i)) (initial xs ys zs))));
        change (φ 0) with 0%Z.
      - pose proof (to_Z_bounded n). lia.
      - reflexivity.
      - intros i acc Hi IH.
        destruct (Side i ltac:(lia)) as [_ Hnth].
        rewrite (succ_small i n) by lia.
        rewrite Z2Nat.inj_add, Nat.add_1_r by lia.
        rewrite (firstn_S_nth _ _ _ _ Hnth), xorG_app, toN_lxor, IH.
        cbn [xorG fold_right Gc]. rewrite N.lxor_0_r. unfold g. rewrite gL_toN.
        reflexivity. }
    rewrite H. f_equal. apply firstn_all2. rewrite Hlen. lia. }
  destruct (sprague_grundy Mn g Hg0 Hmex (initial xs ys zs) Hbd) as [HW HLs].
  destruct (gx =? 0) eqn:E.
  - apply eqb_spec in E. rewrite E in Hgx. change (toN 0) with 0%N in Hgx.
    exists (opponent s). split; [reflexivity|].
    pose proof (HLs (eq_sym Hgx)) as Hl. split.
    + split; [intros H; exfalso; exact (opponent_neq s H)|].
      intros Hw. exfalso. exact (wins_loses_excl _ Hw Hl).
    + split; [intros _; exact Hl | intros _; reflexivity].
  - apply eqb_false_spec in E.
    assert (Hne : xorG g (initial xs ys zs) <> 0%N).
    { rewrite <- Hgx. intro H. apply E. apply toN_inj. exact H. }
    pose proof (HW Hne) as Hw.
    exists s. split; [reflexivity|]. split.
    + split; [intros _; exact Hw | intros _; reflexivity].
    + split; [intros H; exfalso; exact (opponent_neq s (eq_sym H))|].
      intros Hl. exfalso. exact (wins_loses_excl _ Hw Hl).
Qed.

Definition winner_correct :
  forall (s : player) (xs ys zs : list N)
         (s' : player) (a b c : array uint),
  valid_input xs ys zs -> repr s' s -> repr a xs -> repr b ys -> repr c zs ->
  exists o : player, repr (winner s' a b c) o /\ winner_spec s xs ys zs o
  := winner_impl_correct.
