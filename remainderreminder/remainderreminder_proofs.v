(* Correctness proofs for remainderreminder_implem.v. *)
(* Implementation of remainderreminder (remainderreminder.spec).

   Code.  Phase 1 ([scan]): one pass over the corner cuts x = 1 .. with
   2x < a (that is x < (a+1)/2; a <= b), keeping the three largest distinct
   volumes x (a-2x) (b-2x) seen so far in a triple, 0 standing for "none
   yet" (every volume is at least 1).  No table, no sort.
   Phase 2 ([merge], twice): general Chinese remaindering.  [egcd] is the
   iterative extended Euclidean algorithm on (m1, m2): it returns
   g = gcd(m1, m2) and a Bezout coefficient s with s m1 = g (mod m2); the
   coefficient is kept reduced modulo m2 (in [0, m2)), so that no value is
   ever negative and every product stays below 2^60.  The pair
   n = r1 (m1), n = r2 (m2) is rejected when g does not divide r2 - r1,
   otherwise merged into n = r1 + m1 k (mod m1 (m2/g)), with
   k = ((r2 - r1)/g) s mod (m2/g).  The answer is then the least n >= f in
   the final class ([lift]), a constant number of divisions.
   Everything is Uint63 [int]; no Z, no N, no list, no array.

   Termination: [scan] on an erased [Acc (Zwf 0) (gap m x)], [egcd] on an
   erased [Acc (Zwf 0) (φ r1)] (the remainder decreases); no nat, no fuel. *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith Uint63 ZifyUint63 Lia Zwf.

Open Scope uint63_scope.

Require Export remainderreminder_implem.
Open Scope uint63_scope.


Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma scan_eq : forall a b m x t H,
  scan a b m x t H =
  match bdec (x <? m) with
  | left Hx => scan a b m (x + 1) (upd t (vol a b x)) (Acc_inv H (dec_step m x Hx))
  | right _ => t
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma egcd_eq : forall m r0 s0 r1 s1 H,
  egcd m r0 s0 r1 s1 H =
  match bdec (r1 =? 0) with
  | left _ => (r0, s0)
  | right Hn =>
      egcd m r1 s1 (r0 mod r1) ((s0 + m - (r0 / r1) mod m * s1 mod m) mod m)
        (Acc_inv H (mod_dec r0 r1 Hn))
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Uint63 arithmetic                                                   *)
(* ------------------------------------------------------------------ *)

Open Scope Z_scope.

Lemma phi_ge0 : forall x : int, 0 <= (φ x).
Proof. intros x. pose proof (to_Z_bounded x). lia. Qed.

Lemma mul_exact : forall x y : int, (φ x) * (φ y) < wB -> (φ (x * y)) = (φ x) * (φ y).
Proof.
  intros x y H. rewrite mul_spec. apply Z.mod_small.
  pose proof (phi_ge0 x). pose proof (phi_ge0 y).
  split; [apply Z.mul_nonneg_nonneg|]; lia.
Qed.

Lemma add_exact : forall x y : int, (φ x) + (φ y) < wB -> (φ (x + y)) = (φ x) + (φ y).
Proof.
  intros x y H. rewrite add_spec. apply Z.mod_small.
  pose proof (phi_ge0 x). pose proof (phi_ge0 y). lia.
Qed.

Lemma sub_exact : forall x y : int, (φ y) <= (φ x) -> (φ (x - y)) = (φ x) - (φ y).
Proof.
  intros x y H. rewrite sub_spec. apply Z.mod_small.
  pose proof (to_Z_bounded x). pose proof (phi_ge0 y). lia.
Qed.

Lemma ltb_true : forall x y : int, (x <? y)%uint63 = true -> (φ x) < (φ y).
Proof. intros x y H. apply ltb_spec. exact H. Qed.

Lemma ltb_false : forall x y : int, (x <? y)%uint63 = false -> (φ y) <= (φ x).
Proof.
  intros x y H. destruct (Z_lt_le_dec (φ x) (φ y)) as [L|L]; [|exact L].
  apply ltb_spec in L. congruence.
Qed.

Lemma eqb_true : forall x y : int, (x =? y)%uint63 = true -> (φ x) = (φ y).
Proof. intros x y H. apply eqb_spec in H. subst. reflexivity. Qed.

Lemma eqb_false : forall x y : int, (x =? y)%uint63 = false -> (φ x) <> (φ y).
Proof.
  intros x y H E. apply to_Z_inj in E. subst.
  rewrite eqb_false_spec in H. apply H. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Phase 1: the three largest distinct volumes                         *)
(* ------------------------------------------------------------------ *)

(* T1 > T2 > T3 are the largest distinct elements of P, 0 for absent. *)
Definition top3 (P : Z -> Prop) (T1 T2 T3 : Z) : Prop :=
  0 <= T3 /\ T3 <= T2 /\ T2 <= T1 /\
  (0 < T2 -> T2 < T1) /\ (0 < T3 -> T3 < T2) /\
  (0 < T1 -> P T1) /\ (0 < T2 -> P T2) /\ (0 < T3 -> P T3) /\
  (forall v, P v -> v = T1 \/ v = T2 \/ v = T3 \/ v < T3).

Definition top3t (P : Z -> Prop) (t : int * int * int) : Prop :=
  top3 P (φ (fst (fst t))) (φ (snd (fst t))) (φ (snd t)).

Lemma upd_spec : forall (P Q : Z -> Prop) (t : int * int * int) (v : int),
  top3t P t -> 0 < (φ v) ->
  (forall w, Q w <-> P w \/ w = (φ v)) ->
  top3t Q (upd t v).
Proof.
  intros P Q [[t1 t2] t3] v
    (H0 & H12 & H23 & Hs2 & Hs3 & P1 & P2 & P3 & Hc) Hv HQ.
  cbn [fst snd] in *.
  unfold upd.
  destruct (t1 <? v)%uint63 eqn:E1; [apply ltb_true in E1 | apply ltb_false in E1];
  [| destruct (v =? t1)%uint63 eqn:E2; [apply eqb_true in E2 | apply eqb_false in E2];
     [| destruct (t2 <? v)%uint63 eqn:E3; [apply ltb_true in E3 | apply ltb_false in E3];
        [| destruct (v =? t2)%uint63 eqn:E4; [apply eqb_true in E4 | apply eqb_false in E4];
           [| destruct (t3 <? v)%uint63 eqn:E5; [apply ltb_true in E5 | apply ltb_false in E5]]]]];
  unfold top3t, top3; cbn [fst snd];
  repeat split; try lia;
  try (intros Hp; apply HQ;
       first [ right; lia
             | left; first [apply P1 | apply P2 | apply P3]; lia ]);
  try (intros w Hw; apply HQ in Hw; destruct Hw as [Hw | Hw];
       [specialize (Hc w Hw); lia | lia]).
Qed.

(* The volumes of the cuts 1 <= X < x. *)
Definition SZ (A B x v : Z) : Prop :=
  exists X, (1 <= X < x) /\ 2 * X < A /\ 2 * X < B /\
            v = X * (A - 2 * X) * (B - 2 * X).

Lemma SZ_pos : forall A B x v, SZ A B x v -> 0 < v.
Proof.
  intros A B x v (X & HX & HA & HB & ->).
  apply Z.mul_pos_pos; [apply Z.mul_pos_pos|]; lia.
Qed.

Lemma SZ_le : forall A B x v, A <= 100 -> B <= 100 -> SZ A B x v -> v <= 1000000.
Proof.
  intros A B x v HA HB (X & HX & HA' & HB' & ->).
  assert (E1 : X * (A - 2 * X) <= 100 * 100).
  { apply Z.mul_le_mono_nonneg; lia. }
  assert (E2 : X * (A - 2 * X) * (B - 2 * X) <= (100 * 100) * 100).
  { apply Z.mul_le_mono_nonneg; try lia; apply Z.mul_nonneg_nonneg; lia. }
  lia.
Qed.

Lemma vol_spec : forall a b x : int, (φ a) <= 100 -> (φ b) <= 100 ->
  2 * (φ x) < (φ a) -> 2 * (φ x) < (φ b) ->
  (φ (vol a b x)) = (φ x) * ((φ a) - 2 * (φ x)) * ((φ b) - 2 * (φ x)).
Proof.
  intros a b x Ha Hb Hxa Hxb. unfold vol.
  pose proof (phi_ge0 x).
  assert (Ea : (φ (a - 2 * x))%uint63 = (φ a) - 2 * (φ x)) by sia.
  assert (Eb : (φ (b - 2 * x))%uint63 = (φ b) - 2 * (φ x)) by sia.
  assert (B1 : (φ x) * ((φ a) - 2 * (φ x)) <= 100 * 100)
    by (apply Z.mul_le_mono_nonneg; lia).
  assert (E1 : (φ (x * (a - 2 * x)))%uint63 = (φ x) * ((φ a) - 2 * (φ x))).
  { rewrite mul_exact; rewrite Ea; [reflexivity | rewrite wB_val; lia]. }
  rewrite mul_exact; rewrite E1, Eb; [reflexivity|].
  assert (B2 : (φ x) * ((φ a) - 2 * (φ x)) * ((φ b) - 2 * (φ x)) <= (100 * 100) * 100).
  { apply Z.mul_le_mono_nonneg; try lia; apply Z.mul_nonneg_nonneg; lia. }
  rewrite wB_val; lia.
Qed.

Lemma scan_spec : forall a b m : int,
  (φ a) <= (φ b) -> (φ b) <= 100 ->
  (forall X, 0 <= X -> (X < (φ m) <-> 2 * X < (φ a))) ->
  forall (z : Z) (x : int) (t : int * int * int) (H : Acc (Zwf 0) (gap m x)),
  gap m x = z -> 1 <= (φ x) -> (φ x) <= (φ m) ->
  top3t (SZ (φ a) (φ b) (φ x)) t ->
  top3t (SZ (φ a) (φ b) (φ m)) (scan a b m x t H).
Proof.
  intros a b m Hab Hb Hm z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros x t H Hz Hx1 Hxm Ht.
  rewrite scan_eq.
  destruct (bdec (x <? m)%uint63) as [Hx | Hx].
  - pose proof Hx as Hx'. apply ltb_true in Hx'.
    assert (Hx1' : (φ (x + 1))%uint63 = (φ x) + 1) by sia.
    assert (H2a : 2 * (φ x) < (φ a)) by (apply Hm; lia).
    eapply IH; [ | reflexivity | lia | lia | ].
    + rewrite <- Hz. apply dec_step. exact Hx.
    + apply (upd_spec (SZ (φ a) (φ b) (φ x))); [exact Ht | |].
      * rewrite vol_spec by lia.
        apply Z.mul_pos_pos; [apply Z.mul_pos_pos|]; lia.
      * intros w. rewrite Hx1'. rewrite vol_spec by lia. split.
        -- intros (X & HX & HA & HB & ->).
           destruct (Z.eq_dec X (φ x)) as [->|NE]; [right; reflexivity|].
           left. exists X. repeat split; lia.
        -- intros [(X & HX & HA & HB & ->) | ->].
           ++ exists X. repeat split; lia.
           ++ exists (φ x). repeat split; lia.
  - apply ltb_false in Hx. replace (φ m) with (φ x) by lia. exact Ht.
Qed.

(* The volumes of the spec, read as SZ at the end of the scan. *)
Lemma box_iff : forall (a b v : N) (M : Z), (a <= b)%N ->
  (forall X, 0 <= X -> (X < M <-> 2 * X < Z.of_N a)) ->
  (box_size a b v <-> SZ (Z.of_N a) (Z.of_N b) M (Z.of_N v)).
Proof.
  intros a b v M Hab HM. split.
  - intros (x & (H1 & H2 & H3) & ->). exists (Z.of_N x).
    assert (2 * Z.of_N x < Z.of_N a) by lia.
    split; [split; [lia | apply HM; lia] |]. split; [lia|]. split; [lia|].
    rewrite !N2Z.inj_mul, !N2Z.inj_sub by lia. rewrite N2Z.inj_mul. reflexivity.
  - intros (X & HX & HA & HB & E). exists (Z.to_N X).
    split; [unfold cut_ok; lia|].
    apply N2Z.inj. rewrite E.
    rewrite !N2Z.inj_mul, !N2Z.inj_sub by lia.
    rewrite N2Z.inj_mul, Z2N.id by lia. reflexivity.
Qed.

(* The triple of the scan is the spec's three largest. *)
Lemma top3_three_largest : forall (a b w1 w2 w3 : N) (P : Z -> Prop) T1 T2 T3,
  (forall v : N, box_size a b v <-> P (Z.of_N v)) ->
  (forall z, P z -> 0 < z) ->
  top3 P T1 T2 T3 -> three_largest a b w1 w2 w3 ->
  Z.of_N w1 = T1 /\ Z.of_N w2 = T2 /\ Z.of_N w3 = T3.
Proof.
  intros a b w1 w2 w3 P T1 T2 T3 HP Hpos
    (H0 & H12 & H23 & Hs2 & Hs3 & P1 & P2 & P3 & Hc) (B1 & B2 & B3 & Hord & Hw).
  apply HP in B1, B2, B3.
  pose proof (Hpos _ B1). pose proof (Hpos _ B2). pose proof (Hpos _ B3).
  pose proof (Hc _ B1) as C1. pose proof (Hc _ B2) as C2. pose proof (Hc _ B3) as C3.
  assert (HT3 : 0 < T3).
  { destruct C1 as [?|[?|[?|?]]]; destruct C2 as [?|[?|[?|?]]];
      destruct C3 as [?|[?|[?|?]]]; lia. }
  assert (Q : forall T, 0 < T -> P T ->
            T = Z.of_N w1 \/ T = Z.of_N w2 \/ T = Z.of_N w3 \/ T < Z.of_N w3).
  { intros T HT PT. rewrite <- (Z2N.id T) in PT by lia. apply HP in PT.
    destruct (Hw _ PT) as [E|[E|[E|E]]]; lia. }
  pose proof (Q T1 ltac:(lia) (P1 ltac:(lia))) as D1.
  pose proof (Q T2 ltac:(lia) (P2 ltac:(lia))) as D2.
  pose proof (Q T3 ltac:(lia) (P3 ltac:(lia))) as D3.
  assert (E1 : Z.of_N w1 = T1)
    by (clear C2 C3 D2 D3; destruct C1 as [?|[?|[?|?]]]; destruct D1 as [?|[?|[?|?]]]; lia).
  assert (E2 : Z.of_N w2 = T2)
    by (clear C1 C3 D1 D3; destruct C2 as [?|[?|[?|?]]]; destruct D2 as [?|[?|[?|?]]]; lia).
  assert (E3 : Z.of_N w3 = T3)
    by (clear C1 C2 D1 D2; destruct C3 as [?|[?|[?|?]]]; destruct D3 as [?|[?|[?|?]]]; lia).
  auto.
Qed.

(* ------------------------------------------------------------------ *)
(* Phase 2: extended Euclid and the merge of two congruences           *)
(* ------------------------------------------------------------------ *)

Lemma mod_eq_divide : forall n x y, 0 < n -> x mod n = y mod n -> (n | x - y).
Proof.
  intros n x y Hn E. apply Z.mod_divide; [lia|].
  rewrite Zminus_mod, E, Z.sub_diag. reflexivity.
Qed.

Lemma divide_mod_eq : forall n x y, 0 < n -> (n | x - y) -> x mod n = y mod n.
Proof.
  intros n x y Hn [k Hk]. replace x with (y + k * n) by lia.
  apply Z.mod_add. lia.
Qed.

Lemma egcd_step_div : forall M M1 R0 R1 S0 S1, 0 < M -> R1 <> 0 ->
  (M | R0 - S0 * M1) -> (M | R1 - S1 * M1) ->
  (M | R0 mod R1 - ((S0 + M - (R0 / R1) mod M * S1 mod M) mod M) * M1).
Proof.
  intros M M1 R0 R1 S0 S1 HM HR [k0 Hk0] [k1 Hk1].
  rewrite (Z.mod_eq (S0 + M - (R0 / R1) mod M * S1 mod M) M) by lia.
  rewrite (Z.mod_eq ((R0 / R1) mod M * S1) M) by lia.
  rewrite (Z.mod_eq (R0 / R1) M) by lia.
  rewrite (Z.mod_eq R0 R1) by lia.
  generalize (R0 / R1) as q. intros q.
  generalize (q / M) as a. intros a.
  generalize ((q - M * a) * S1 / M) as b. intros b.
  generalize ((S0 + M - ((q - M * a) * S1 - M * b)) / M) as c. intros c.
  exists (k0 - q * k1 - M1 - a * S1 * M1 - b * M1 + c * M1).
  replace R0 with (k0 * M + S0 * M1) by lia.
  replace R1 with (k1 * M + S1 * M1) by lia.
  ring.
Qed.

Lemma egcd_spec : forall (M1 : Z) (m : int), 0 < (φ m) < 2 ^ 30 ->
  forall (z : Z) (r0 s0 r1 s1 : int) (H : Acc (Zwf 0) (φ r1)),
  (φ r1) = z -> (φ s0) < (φ m) -> (φ s1) < (φ m) ->
  ((φ m) | (φ r0) - (φ s0) * M1) -> ((φ m) | (φ r1) - (φ s1) * M1) ->
  (φ (fst (egcd m r0 s0 r1 s1 H))) = Z.gcd (φ r0) (φ r1) /\
  (φ (snd (egcd m r0 s0 r1 s1 H))) < (φ m) /\
  ((φ m) | (φ (fst (egcd m r0 s0 r1 s1 H))) - (φ (snd (egcd m r0 s0 r1 s1 H))) * M1).
Proof.
  intros M1 m Hm z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros r0 s0 r1 s1 H Hz Hs0 Hs1 D0 D1.
  rewrite egcd_eq.
  destruct (bdec (r1 =? 0)%uint63) as [E | E].
  - apply eqb_spec in E. subst r1. cbn [fst snd].
    change ((φ 0)%uint63) with 0. rewrite Z.gcd_0_r, Z.abs_eq by apply phi_ge0.
    auto.
  - pose proof E as Nr1. apply eqb_false in Nr1. change ((φ 0)%uint63) with 0 in Nr1.
    pose proof (phi_ge0 r0). pose proof (phi_ge0 r1).
    pose proof (phi_ge0 s0). pose proof (phi_ge0 s1).
    assert (Eq : (φ ((r0 / r1) mod m))%uint63 = ((φ r0) / (φ r1)) mod (φ m))
      by (rewrite mod_spec, div_spec; reflexivity).
    pose proof (Z.mod_pos_bound ((φ r0) / (φ r1)) (φ m) ltac:(lia)) as Bq.
    assert (Eqs : (φ ((r0 / r1) mod m * s1))%uint63 = ((φ r0) / (φ r1)) mod (φ m) * (φ s1)).
    { rewrite mul_exact; rewrite Eq; [reflexivity|].
      assert (((φ r0) / (φ r1)) mod (φ m) * (φ s1) <= (φ m) * (φ m)) by
        (apply Z.mul_le_mono_nonneg; lia).
      assert ((φ m) * (φ m) <= 2 ^ 30 * 2 ^ 30) by (apply Z.mul_le_mono_nonneg; lia).
      rewrite wB_val. lia. }
    assert (Ew : (φ ((r0 / r1) mod m * s1 mod m))%uint63
                 = (((φ r0) / (φ r1)) mod (φ m) * (φ s1)) mod (φ m))
      by (rewrite mod_spec, Eqs; reflexivity).
    pose proof (Z.mod_pos_bound (((φ r0) / (φ r1)) mod (φ m) * (φ s1)) (φ m) ltac:(lia)) as Bw.
    assert (Ea : (φ (s0 + m))%uint63 = (φ s0) + (φ m))
      by (apply add_exact; rewrite wB_val; lia).
    assert (Eb : (φ (s0 + m - (r0 / r1) mod m * s1 mod m))%uint63
                 = (φ s0) + (φ m) - (((φ r0) / (φ r1)) mod (φ m) * (φ s1)) mod (φ m)).
    { rewrite sub_exact; rewrite Ea, Ew; [reflexivity | lia]. }
    assert (Es : (φ ((s0 + m - (r0 / r1) mod m * s1 mod m) mod m))%uint63
                 = ((φ s0) + (φ m) - ((φ r0) / (φ r1)) mod (φ m) * (φ s1) mod (φ m)) mod (φ m))
      by (rewrite mod_spec, Eb; reflexivity).
    assert (Hs' : (φ ((s0 + m - (r0 / r1) mod m * s1 mod m) mod m))%uint63 < (φ m)).
    { rewrite Es. apply Z.mod_pos_bound. lia. }
    assert (Dn : ((φ m) | (φ (r0 mod r1))%uint63
                        - (φ ((s0 + m - (r0 / r1) mod m * s1 mod m) mod m))%uint63 * M1)).
    { rewrite Es, mod_spec. apply egcd_step_div; auto; lia. }
    assert (Hd : Zwf 0 ((φ (r0 mod r1))%uint63) z) by (rewrite <- Hz; apply mod_dec; exact E).
    destruct (IH _ Hd r1 s1 (r0 mod r1)%uint63 _ (Acc_inv H (mod_dec r0 r1 E))
                eq_refl Hs1 Hs' D1 Dn) as (G1 & G2 & G3).
    split; [|split; assumption].
    rewrite G1, mod_spec, Z.gcd_comm, Z.gcd_mod by exact Nr1.
    apply Z.gcd_comm.
Qed.

Lemma init_div : forall M M1, 0 < M -> (M | M1 - (1 mod M) * M1).
Proof.
  intros M M1 HM. rewrite (Z.mod_eq 1 M) by lia.
  exists ((1 / M) * M1). ring.
Qed.

Lemma dd_div : forall M R1 R2, 0 < M -> (M | (R2 + M - R1 mod M) mod M - (R2 - R1)).
Proof.
  intros M R1 R2 HM.
  rewrite (Z.mod_eq (R2 + M - R1 mod M) M) by lia.
  rewrite (Z.mod_eq R1 M) by lia.
  generalize (R1 / M) as a. intros a.
  generalize ((R2 + M - (R1 - M * a)) / M) as c. intros c.
  exists (1 + a - c). ring.
Qed.

(* The arithmetic of [merge], on Z alone. *)
Lemma merge_arith : forall R1 M1 R2 M2 G S X DD D M2' K : Z,
  0 <= R1 < M1 -> 0 <= R2 < M2 -> 0 < M2 ->
  X mod M1 = R1 -> X mod M2 = R2 ->
  G = Z.gcd M1 M2 -> 0 <= S < M2 -> (M2 | G - S * M1) ->
  DD = (R2 + M2 - R1 mod M2) mod M2 -> D = DD / G -> M2' = M2 / G ->
  K = (D * S) mod M2' ->
  DD mod G = 0 /\ 0 <= D < M2 /\ 1 <= M2' <= M2 /\ 0 <= K < M2' /\
  0 <= R1 + M1 * K /\ M1 * K + M1 <= M1 * M2' /\ M1 * M2' <= M1 * M2 /\
  forall n, (n mod M1 = R1 /\ n mod M2 = R2) <-> n mod (M1 * M2') = R1 + M1 * K.
Proof.
  intros R1 M1 R2 M2 G S X DD D M2' K HR1 HR2 HM2p HX1 HX2 HG HS G3 EDD ED EM2' EK.
  assert (Hm1 : 0 < M1) by lia.
  assert (Gd1 : (G | M1)) by (rewrite HG; apply Z.gcd_divide_l).
  assert (Gd2 : (G | M2)) by (rewrite HG; apply Z.gcd_divide_r).
  assert (Gpos : 0 < G).
  { assert (0 <= G) by (rewrite HG; apply Z.gcd_nonneg).
    destruct (Z.eq_dec G 0) as [E0|E0]; [|lia].
    rewrite E0 in Gd2. destruct Gd2 as [k Hk]. lia. }
  assert (Gle : G <= M2) by (apply Z.divide_pos_le; [lia | exact Gd2]).
  assert (HM2 : M2 = G * M2')
    by (rewrite EM2'; apply Z.div_exact; [lia | apply Z.mod_divide; [lia | exact Gd2]]).
  assert (HM1 : M1 = G * (M1 / G))
    by (apply Z.div_exact; [lia | apply Z.mod_divide; [lia | exact Gd1]]).
  pose proof (Z.mod_pos_bound (R2 + M2 - R1 mod M2) M2 HM2p) as Bdd.
  rewrite <- EDD in Bdd.
  pose proof (dd_div M2 R1 R2 HM2p) as Hdd. rewrite <- EDD in Hdd.
  (* compatibility *)
  assert (Gc : (G | DD)).
  { assert (A1 : (M1 | X - R1))
      by (apply mod_eq_divide; [lia | rewrite HX1; symmetry; apply Z.mod_small; lia]).
    assert (A2 : (M2 | X - R2))
      by (apply mod_eq_divide; [lia | rewrite HX2; symmetry; apply Z.mod_small; lia]).
    assert (A3 : (G | R2 - R1)).
    { replace (R2 - R1) with ((X - R1) - (X - R2)) by ring.
      apply Z.divide_sub_r;
        [apply (Z.divide_trans _ M1) | apply (Z.divide_trans _ M2)]; assumption. }
    replace DD with ((DD - (R2 - R1)) + (R2 - R1)) by ring.
    apply Z.divide_add_r; [apply (Z.divide_trans _ M2); assumption | exact A3]. }
  assert (Ecomp : DD mod G = 0) by (apply Z.mod_divide; [lia | exact Gc]).
  assert (BM2' : 1 <= M2' <= M2).
  { rewrite EM2'. split.
    - apply Z.div_le_lower_bound; lia.
    - apply Z.div_le_upper_bound; [lia|].
      rewrite <- (Z.mul_1_l M2) at 1. apply Z.mul_le_mono_nonneg_r; lia. }
  assert (HDD : DD = G * D)
    by (rewrite ED; apply Z.div_exact; [lia | exact Ecomp]).
  assert (BD : 0 <= D < M2).
  { rewrite ED. split.
    - apply Z.div_pos; lia.
    - apply (Z.le_lt_trans _ DD); [|apply Bdd].
      apply Z.div_le_upper_bound; [lia|].
      rewrite <- (Z.mul_1_l DD) at 1. apply Z.mul_le_mono_nonneg_r; lia. }
  pose proof (Z.mod_pos_bound (D * S) M2' ltac:(lia)) as BK. rewrite <- EK in BK.
  assert (BMK : M1 * K + M1 <= M1 * M2').
  { replace (M1 * K + M1) with (M1 * (K + 1)) by ring.
    apply Z.mul_le_mono_nonneg_l; lia. }
  assert (BMM : M1 * M2' <= M1 * M2) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (BK0 : 0 <= M1 * K) by (apply Z.mul_nonneg_nonneg; lia).
  assert (HM12 : M1 * M2' = (M1 / G) * M2).
  { rewrite HM2. rewrite HM1 at 1. ring. }
  (* the merged representative satisfies both congruences *)
  assert (HN1 : (R1 + M1 * K) mod M1 = R1).
  { rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (HN2 : (R1 + M1 * K) mod M2 = R2).
  { rewrite <- (Z.mod_small R2 M2) by lia.
    apply divide_mod_eq; [lia|].
    destruct G3 as [j Hj]. destruct Hdd as [i Hi].
    assert (EK' : K = D * S - M2' * (D * S / M2')) by (rewrite EK; apply Z.mod_eq; lia).
    exists (i - D * j - (M1 / G) * (D * S / M2')).
    rewrite EK'.
    assert (ESM : S * M1 = G - j * M2) by lia.
    replace (R1 + M1 * (D * S - M2' * (D * S / M2')) - R2)
      with (R1 - R2 + D * (S * M1) - (M1 * M2') * (D * S / M2'))
      by ring.
    rewrite ESM, HM12.
    replace (D * (G - j * M2)) with (G * D - D * j * M2) by ring.
    rewrite <- HDD. lia. }
  assert (HL1 : (M1 | M1 * M2')) by (exists M2'; ring).
  assert (HL2 : (M2 | M1 * M2')) by (rewrite HM12; exists (M1 / G); ring).
  assert (Hlcm : Z.lcm M1 M2 = M1 * M2').
  { unfold Z.lcm. rewrite <- HG, <- EM2'. apply Z.abs_eq. lia. }
  split; [exact Ecomp|]. split; [exact BD|]. split; [exact BM2'|]. split; [exact BK|].
  split; [lia|]. split; [exact BMK|]. split; [exact BMM|].
  assert (HL0 : 0 < M1 * M2') by lia.
  assert (HB0 : 0 <= R1 + M1 * K < M1 * M2') by lia.
  clear - HL0 HB0 Hm1 HM2p HN1 HN2 HL1 HL2 Hlcm.
  intros n. split.
  - intros [h1 h2].
    rewrite <- (Z.mod_small (R1 + M1 * K) (M1 * M2')) by exact HB0.
    apply divide_mod_eq; [exact HL0|].
    rewrite <- Hlcm. apply Z.lcm_least.
    + apply mod_eq_divide; [exact Hm1|]. rewrite h1, HN1. reflexivity.
    + apply mod_eq_divide; [exact HM2p|]. rewrite h2, HN2. reflexivity.
  - intros h.
    assert (Hd : (M1 * M2' | n - (R1 + M1 * K))).
    { apply mod_eq_divide; [exact HL0|]. rewrite h. symmetry. apply Z.mod_small. exact HB0. }
    split.
    + rewrite <- HN1. apply divide_mod_eq; [exact Hm1|].
      apply (Z.divide_trans _ (M1 * M2')); assumption.
    + rewrite <- HN2. apply divide_mod_eq; [exact HM2p|].
      apply (Z.divide_trans _ (M1 * M2')); assumption.
Qed.

Lemma merge_spec : forall r1 m1 r2 m2 : int,
  (φ r1) < (φ m1) -> (φ r2) < (φ m2) -> 0 < (φ m2) < 2 ^ 30 -> (φ m1) * (φ m2) < 2 ^ 62 ->
  (exists X, X mod (φ m1) = (φ r1) /\ X mod (φ m2) = (φ r2)) ->
  forall rn ln, merge r1 m1 r2 m2 = (rn, ln) ->
  0 <= (φ rn) < (φ ln) /\ (φ ln) <= (φ m1) * (φ m2) /\
  forall n, (n mod (φ m1) = (φ r1) /\ n mod (φ m2) = (φ r2)) <-> n mod (φ ln) = (φ rn).
Proof.
  intros r1 m1 r2 m2 Hr1 Hr2 Hm2 Hprod [X [HX1 HX2]] rn ln Em.
  pose proof (phi_ge0 r1). pose proof (phi_ge0 r2).
  pose proof (phi_ge0 m1). pose proof (phi_ge0 m2).
  assert (B1 : (φ (1 mod m2))%uint63 < (φ m2))
    by (rewrite mod_spec; apply Z.mod_pos_bound; lia).
  assert (D0 : ((φ m2) | (φ m1) - (φ (1 mod m2))%uint63 * (φ m1)))
    by (rewrite mod_spec; apply init_div; lia).
  assert (D1 : ((φ m2) | (φ m2) - (φ 0)%uint63 * (φ m1)))
    by (change ((φ 0)%uint63) with 0; exists 1; ring).
  destruct (egcd_spec (φ m1) m2 Hm2 _ m1 (1 mod m2)%uint63 m2 0%uint63
              (Zwf_well_founded 0 (φ m2)) eq_refl B1 ltac:(change ((φ 0)%uint63) with 0; lia)
              D0 D1) as (G1 & G2 & G3).
  unfold merge in Em.
  destruct (egcd m2 m1 (1 mod m2) m2 0 (Zwf_well_founded 0 (φ m2)))%uint63
    as [g s] eqn:Eg.
  cbn [fst snd] in G1, G2, G3.
  pose proof (phi_ge0 s).
  clear B1 D0 D1 Eg.
  (* dd *)
  assert (Er : (φ (r1 mod m2))%uint63 = (φ r1) mod (φ m2)) by apply mod_spec.
  pose proof (Z.mod_pos_bound (φ r1) (φ m2) ltac:(lia)) as Br.
  assert (E2 : (φ (r2 + m2))%uint63 = (φ r2) + (φ m2))
    by (apply add_exact; rewrite wB_val; lia).
  assert (E3 : (φ (r2 + m2 - r1 mod m2))%uint63 = (φ r2) + (φ m2) - (φ r1) mod (φ m2)).
  { rewrite sub_exact; rewrite E2, Er; [reflexivity | lia]. }
  assert (Edd : (φ ((r2 + m2 - r1 mod m2) mod m2))%uint63
                = ((φ r2) + (φ m2) - (φ r1) mod (φ m2)) mod (φ m2))
    by (rewrite mod_spec, E3; reflexivity).
  clear Er E2 E3 Br.
  destruct (merge_arith (φ r1) (φ m1) (φ r2) (φ m2) (φ g) (φ s) X
              _ _ _ _ ltac:(lia) ltac:(lia) ltac:(lia) HX1 HX2 G1 ltac:(lia) G3
              Edd eq_refl eq_refl eq_refl)
    as (Ecomp & BD & BM2' & BK & BK0 & BMK & BMM & Heq).
  assert (Ecomp' : (((r2 + m2 - r1 mod m2) mod m2) mod g =? 0)%uint63 = true).
  { apply eqb_spec. apply to_Z_inj. rewrite mod_spec. exact Ecomp. }
  cbv beta iota zeta in Em. rewrite Ecomp' in Em.
  injection Em as Ern Eln. subst rn ln.
  clear Ecomp Ecomp'.
  set (dd := ((r2 + m2 - r1 mod m2) mod m2)%uint63) in *.
  assert (Em2 : (φ (m2 / g))%uint63 = (φ m2) / (φ g)) by apply div_spec.
  assert (Ed : (φ (dd / g))%uint63 = (φ dd) / (φ g)) by apply div_spec.
  set (M2' := (φ m2) / (φ g)) in *.
  set (D := (φ dd) / (φ g)) in *.
  assert (Eds : (φ (dd / g * s))%uint63 = D * (φ s)).
  { rewrite mul_exact; rewrite Ed; [reflexivity|].
    assert (Q1 : D * (φ s) <= (φ m2) * (φ m2)) by (apply Z.mul_le_mono_nonneg; lia).
    assert (Q2 : (φ m2) * (φ m2) <= 2 ^ 30 * 2 ^ 30) by (apply Z.mul_le_mono_nonneg; lia).
    rewrite wB_val. clear - Q1 Q2. lia. }
  assert (Ek : (φ ((dd / g * s) mod (m2 / g)))%uint63 = (D * (φ s)) mod M2')
    by (rewrite mod_spec, Eds, Em2; reflexivity).
  set (K := (D * (φ s)) mod M2') in *.
  assert (Emk : (φ (m1 * ((dd / g * s) mod (m2 / g))))%uint63 = (φ m1) * K).
  { rewrite mul_exact; rewrite Ek; [reflexivity|]. rewrite wB_val.
    clear - BMK BMM Hprod H1 BK0; lia. }
  assert (En : (φ (r1 + m1 * ((dd / g * s) mod (m2 / g))))%uint63 = (φ r1) + (φ m1) * K).
  { rewrite add_exact; rewrite Emk; [reflexivity|]. rewrite wB_val.
    clear - BMK BMM Hprod Hr1 H1 BK0; lia. }
  assert (El : (φ (m1 * (m2 / g)))%uint63 = (φ m1) * M2').
  { rewrite mul_exact; rewrite Em2; [reflexivity|]. rewrite wB_val.
    clear - BMK BMM Hprod H1 BK0; lia. }
  rewrite En, El.
  split; [clear - BMK BK0 Hr1; lia|]. split; [exact BMM | exact Heq].
Qed.

(* ------------------------------------------------------------------ *)
(* The lift into [f, g]                                                *)
(* ------------------------------------------------------------------ *)

Lemma lift_spec : forall f r l : int,
  0 <= (φ r) < (φ l) -> (φ l) <= 10 ^ 18 -> (φ f) <= 10 ^ 9 ->
  (φ (lift f r l)) mod (φ l) = (φ r) /\ (φ f) <= (φ (lift f r l)) /\
  forall n, (φ f) <= n -> n mod (φ l) = (φ r) -> (φ (lift f r l)) <= n.
Proof.
  intros f r l Hr Hl Hf. unfold lift.
  pose proof (phi_ge0 f).
  assert (Efl : (φ (f mod l))%uint63 = (φ f) mod (φ l)) by apply mod_spec.
  pose proof (Z.mod_pos_bound (φ f) (φ l) ltac:(lia)) as Bf.
  assert (E1 : (φ (r + l))%uint63 = (φ r) + (φ l))
    by (apply add_exact; rewrite wB_val; lia).
  assert (E2 : (φ (r + l - f mod l))%uint63 = (φ r) + (φ l) - (φ f) mod (φ l)).
  { rewrite sub_exact; rewrite E1, Efl; [reflexivity | lia]. }
  assert (E3 : (φ ((r + l - f mod l) mod l))%uint63
               = ((φ r) + (φ l) - (φ f) mod (φ l)) mod (φ l))
    by (rewrite mod_spec, E2; reflexivity).
  pose proof (Z.mod_pos_bound ((φ r) + (φ l) - (φ f) mod (φ l)) (φ l) ltac:(lia)) as BY.
  set (Y := ((φ r) + (φ l) - (φ f) mod (φ l)) mod (φ l)) in *.
  assert (E4 : (φ (f + (r + l - f mod l) mod l))%uint63 = (φ f) + Y).
  { rewrite add_exact; rewrite E3; [reflexivity | rewrite wB_val; lia]. }
  rewrite E4.
  assert (HY : Y = ((φ r) - (φ f)) mod (φ l)).
  { unfold Y. apply divide_mod_eq; [lia|].
    rewrite (Z.mod_eq (φ f) (φ l)) by lia.
    exists (1 + (φ f) / (φ l)). ring. }
  split; [|split; [lia|]].
  - rewrite HY, Zplus_mod_idemp_r.
    replace ((φ f) + ((φ r) - (φ f))) with (φ r) by ring.
    apply Z.mod_small. lia.
  - intros n Hn Hnm.
    assert (HY' : Y = (n - (φ f)) mod (φ l)).
    { rewrite HY. apply divide_mod_eq; [lia|].
      rewrite (Z.mod_eq n (φ l)) in Hnm by lia.
      exists (- (n / (φ l))). lia. }
    rewrite HY'. pose proof (Z.mod_le (n - (φ f)) (φ l) ltac:(lia) ltac:(lia)). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Lemma N_mod_Z : forall n v c : N,
  (n mod v = c)%N <-> Z.of_N n mod Z.of_N v = Z.of_N c.
Proof.
  intros n v c. rewrite <- N2Z.inj_mod. split; [intros ->; reflexivity | apply N2Z.inj].
Qed.

Lemma repr_phi : forall (x : uint) (a : N), repr x a -> (φ x) = Z.of_N a.
Proof.
  intros x a H. unfold repr, repr_uint in H. rewrite <- H.
  rewrite Z2N.id; [reflexivity | apply phi_ge0].
Qed.

Theorem rr_impl_correct :
  forall (a b c d e f g : N) (xa xb xc xd xe xf xg : uint),
  valid_input a b c d e f g ->
  repr xa a -> repr xb b -> repr xc c -> repr xd d -> repr xe e ->
  repr xf f -> repr xg g ->
  exists o : N, repr (rr_impl xa xb xc xd xe xf xg) o /\
                remainderreminder_spec a b c d e f g o.
Proof.
  intros a b c d e f g xa xb xc xd xe xf xg Hv Ha Hb Hc Hd He Hf Hg.
  apply repr_phi in Ha, Hb, Hc, Hd, He, Hf, Hg.
  destruct Hv as [Vab Va Vb Vc Vd Ve Vfg Vg Vu].
  destruct Vu as [n0 [Hn0 Hun]].
  pose proof Hn0 as (Hfg0 & w1 & w2 & w3 & Htl & Hm1 & Hm2 & Hm3).
  apply N_mod_Z in Hm1, Hm2, Hm3.
  unfold rr_impl.
  set (m := ((xa + 1) / 2)%uint63).
  assert (Hmv : (φ m) = ((φ xa) + 1) / 2) by (unfold m; sia).
  assert (Hm : forall X, 0 <= X -> (X < (φ m) <-> 2 * X < (φ xa))).
  { intros X HX. rewrite Hmv.
    pose proof (Z.div_mod ((φ xa) + 1) 2 ltac:(lia)).
    pose proof (Z.mod_pos_bound ((φ xa) + 1) 2 ltac:(lia)). lia. }
  assert (Hm0 : 1 <= (φ m)) by (rewrite Hmv; rewrite Ha; apply Z.div_le_lower_bound; lia).
  pose proof (scan_spec xa xb m ltac:(lia) ltac:(lia) Hm _ 1%uint63 (0, 0, 0)%uint63
                (Zwf_well_founded 0 (gap m 1)) eq_refl
                ltac:(change ((φ 1)%uint63) with 1; lia)
                ltac:(change ((φ 1)%uint63) with 1; lia)) as Hscan.
  destruct (scan xa xb m 1 (0, 0, 0) (Zwf_well_founded 0 (gap m 1)))%uint63
    as [[v1 v2] v3] eqn:Es.
  lapply Hscan.
  2:{ unfold top3t, top3. cbn [fst snd]. change ((φ 0)%uint63) with 0.
      change ((φ 1)%uint63) with 1.
      repeat split; try lia. intros v (X & HX & _). lia. }
  clear Hscan. intros Hscan.
  unfold top3t in Hscan. cbn [fst snd] in Hscan.
  assert (HP : forall v : N, box_size a b v <-> SZ (φ xa) (φ xb) (φ m) (Z.of_N v)).
  { intros v. rewrite Ha, Hb. apply box_iff; [exact Vab|]. rewrite <- Ha. exact Hm. }
  destruct (top3_three_largest a b w1 w2 w3 _ _ _ _ HP
              (fun z Hz => SZ_pos _ _ _ _ Hz) Hscan Htl) as (W1 & W2 & W3).
  destruct Hscan as (H0 & H12 & H23 & Hs2 & Hs3 & P1 & P2 & P3 & _).
  rewrite W1, <- Hc in Hm1. rewrite W2, <- Hd in Hm2. rewrite W3, <- He in Hm3.
  assert (Hv3 : 0 < (φ v3)).
  { rewrite <- W3. apply (SZ_pos (φ xa) (φ xb) (φ m)). apply HP.
    destruct Htl as (_ & _ & B3 & _). exact B3. }
  pose proof (Z.mod_pos_bound (Z.of_N n0) (φ v3) ltac:(lia)) as Bc3.
  assert (Bv1 : (φ v1) <= 1000000) by (apply (SZ_le (φ xa) (φ xb) (φ m)); [lia | lia | apply P1; lia]).
  assert (Bv2 : (φ v2) <= 1000000) by (apply (SZ_le (φ xa) (φ xb) (φ m)); [lia | lia | apply P2; lia]).
  assert (Bv3 : (φ v3) <= 1000000) by (apply (SZ_le (φ xa) (φ xb) (φ m)); [lia | lia | apply P3; lia]).
  pose proof (Z.mod_pos_bound (Z.of_N n0) (φ v1) ltac:(lia)) as Bc1.
  pose proof (Z.mod_pos_bound (Z.of_N n0) (φ v2) ltac:(lia)) as Bc2.
  (* first merge *)
  destruct (merge xc v1 xd v2) as [r12 l12] eqn:Em1.
  assert (Bp1 : (φ v1) * (φ v2) <= 1000000 * 1000000)
    by (apply Z.mul_le_mono_nonneg; lia).
  destruct (merge_spec xc v1 xd v2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              (ex_intro _ (Z.of_N n0) (conj Hm1 Hm2)) r12 l12 Em1)
    as (Br12 & Bl12 & Eq1).
  (* second merge *)
  destruct (merge r12 l12 xe v3) as [r l] eqn:Em2.
  assert (Hn012 : Z.of_N n0 mod (φ l12) = (φ r12)) by (apply Eq1; auto).
  assert (Bp2 : (φ l12) * (φ v3) <= (1000000 * 1000000) * 1000000)
    by (apply Z.mul_le_mono_nonneg; lia).
  destruct (merge_spec r12 l12 xe v3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              (ex_intro _ (Z.of_N n0) (conj Hn012 Hm3)) r l Em2)
    as (Br & Bl & Eq2).
  (* the lift *)
  destruct (lift_spec xf r l ltac:(lia) ltac:(lia) ltac:(lia)) as (A1 & A2 & A3).
  set (ANS := (φ (lift xf r l))) in *.
  assert (Hn0r : Z.of_N n0 mod (φ l) = (φ r)) by (apply Eq2; auto).
  assert (A4 : ANS <= Z.of_N n0) by (apply A3; [clear - Hf Hfg0; lia | exact Hn0r]).
  apply Eq2 in A1. destruct A1 as [A12 A5]. apply Eq1 in A12. destruct A12 as [A6 A7].
  assert (Hcons : consistent a b c d e f g (Z.to_N ANS)).
  { assert (ANS0 : 0 <= ANS) by (unfold ANS; apply phi_ge0).
    split; [clear - A2 A4 Hf Hg Hfg0 ANS0; lia|].
    exists w1, w2, w3. split; [exact Htl|].
    rewrite !N_mod_Z, !Z2N.id by exact ANS0. rewrite W1, W2, W3, <- Hc, <- Hd, <- He.
    auto. }
  pose proof (Hun _ Hcons) as En0.
  exists (Z.to_N ANS). split.
  - reflexivity.
  - intros n. split.
    + intros Hn. rewrite <- (Hun _ Hn). exact En0.
    + intros ->. exact Hcons.
Qed.

Definition remainderreminder_correct :
  forall (a b c d e f g : N) (xa xb xc xd xe xf xg : uint),
  valid_input a b c d e f g ->
  repr xa a -> repr xb b -> repr xc c -> repr xd d -> repr xe e ->
  repr xf f -> repr xg g ->
  exists o : N, repr (remainderreminder xa xb xc xd xe xf xg) o /\
                remainderreminder_spec a b c d e f g o
  := rr_impl_correct.
