(* Correctness proofs for slowleak_implem.v. *)
(* Implementation of slowleak (slowleak.spec): Floyd-Warshall on the
   road graph, then an O(V^2) array Dijkstra on the refill points.

   Code.  One flat n*n [array int] T, cell a*n+b for intersections a+1,
   b+1: INF = 2^61 everywhere, 0 on the diagonal ([diag_loop]), then
   T[u][v] := min(T[u][v], k) in both directions for every road
   ([edge_loop]), then Floyd-Warshall in place, pivot k outermost
   ([fw_k] / [fw_i] / [fw_j], T[i][k] read once per row).  Entries never
   exceed INF, so a sum of two entries (< 2^62) never wraps.  Dijkstra
   ([dij_loop]) runs on M = t+2 nodes: node 0 is the school, node a (1 <=
   a <= t) the station xs[a-1], node t+1 home; V (built by [vx_loop]) maps
   a node to its 0-based intersection.  The edge a -> b weighs
   T[V[a]][V[b]] when that is <= d.  Each round selects the unvisited node
   of least finite distance ([sel_loop]); home selected: Some dist; none
   left: None ("stuck"); otherwise it is marked and its edges relaxed
   ([rel_loop]); home is never expanded.  A counter r (M at start) bounds
   the rounds.  No Z, no nat, no list in the code; every array is used
   linearly.

   Termination: every loop recurses on an erased [Acc (Zwf 0) _] proof
   (gap hi i, or phi r for [dij_loop]), as in the template.

   Proof.  [fwinv K T]: entries <= INF, zero diagonal, every entry < INF
   is the length of a walk, every road bounds its cell, and the triangle
   inequality through every pivot < K.  [stepped] describes the table in
   the middle of a pivot step (cells before the flat position q updated);
   row and column k are unchanged during step k because T[k][k] = 0.  With
   K = n, [fw_lower]: no walk is shorter than its cell.  Dijkstra is
   proven on an abstract weight w: [dp a L] (a path from node 0 to a of
   length L, never leaving home), invariant [dji] (sound distances,
   visited distances optimal, relaxed edges), and the cut lemma [cut]:
   every path to an unvisited node passes an unvisited node of distance
   <= its length; [ucnt] counts the unvisited nodes for the r = 0 branch.
   [sound] / [complete] relate dp on the node graph to the spec's [trip]
   (through [fw_lower] and the walks of the table).  The None case uses
   the spec's vi_answer: if some trip existed, a shortest one would
   (double negation, [dn_min]) and be < 2^31 < INF, so Dijkstra would
   have reached home. *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
Import ListNotations.

Open Scope uint63_scope.

Unset Lia Cache.

Require Export slowleak_implem.
Open Scope uint63_scope.


(* ------------------------------------------------------------------ *)
(* Uint63 / PArray plumbing                                            *)
(* ------------------------------------------------------------------ *)

Lemma INF_val : (φ INF) = 2305843009213693952%Z.
Proof. reflexivity. Qed.

Lemma eqbP : forall p q : int, Bool.reflect (p = q) (p =? q).
Proof. intros p q. apply Bool.iff_reflect. symmetry. apply eqb_spec. Qed.

Lemma ltbP : forall p q : int, Bool.reflect ((φ p) < (φ q))%Z (p <? q).
Proof. intros p q. apply Bool.iff_reflect. symmetry. apply ltb_spec. Qed.

Lemma lebP : forall p q : int, Bool.reflect ((φ p) <= (φ q))%Z (p <=? q).
Proof. intros p q. apply Bool.iff_reflect. symmetry. apply leb_spec. Qed.

Lemma aget_set_same : forall (t : array int) (i : int) (b : int),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same int t i b H). Qed.

Lemma aget_set_other : forall (t : array int) (i j : int) (b : int),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other int t i j b H). Qed.

Lemma alength_set : forall (t : array int) (i : int) (b : int),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set int t i b). Qed.

Lemma aget_make : forall (n i b : int), (PArray.make n b).[i] = b.
Proof. intros. exact (get_make int b n i). Qed.

Lemma alength_make : forall (n : int) (b : int),
  PArray.length (PArray.make n b)
  = if n <=? PArray.max_length then n else PArray.max_length.
Proof. intros n b. exact (length_make int n b). Qed.

Lemma bget_set_same : forall (t : array bool) (i : int) (b : bool),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same bool t i b H). Qed.

Lemma bget_set_other : forall (t : array bool) (i j : int) (b : bool),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other bool t i j b H). Qed.

Lemma blength_set : forall (t : array bool) (i : int) (b : bool),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set bool t i b). Qed.

Lemma bget_make : forall (n i : int) (b : bool), (PArray.make n b).[i] = b.
Proof. intros. exact (get_make bool b n i). Qed.

Lemma blength_make : forall (n : int) (b : bool),
  PArray.length (PArray.make n b)
  = if n <=? PArray.max_length then n else PArray.max_length.
Proof. intros n b. exact (length_make bool n b). Qed.

Lemma sub1_val : forall x : int, (1 <= (φ x))%Z -> (φ (x - 1)) = ((φ x) - 1)%Z.
Proof. intros x H. sia. Qed.

Lemma setmin_len : forall T p s, PArray.length (setmin T p s) = PArray.length T.
Proof.
  intros T p s. unfold setmin. destruct (s <? T.[p]); [apply alength_set | reflexivity].
Qed.

Lemma setmin_get : forall T p s q, ((φ p) < (φ (PArray.length T)))%Z ->
  (φ ((setmin T p s).[q])) = if p =? q then Z.min (φ (T.[p])) (φ s) else (φ (T.[q])).
Proof.
  intros T p s q Hp. unfold setmin.
  destruct (eqbP p q) as [E | E].
  - subst q. destruct (ltbP s T.[p]).
    + rewrite aget_set_same by (rewrite ltb_spec; exact Hp). lia.
    + lia.
  - destruct (s <? T.[p]); [rewrite aget_set_other by exact E|]; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Floyd-Warshall                                                      *)
(* ------------------------------------------------------------------ *)

Section FW.

Variable n : int.
Hypothesis Hn : (2 <= (φ n) <= 500)%Z.
Variables ri rj rk : list N.

Definition inr (a : int) : Prop := ((φ a) < (φ n))%Z.
Definition C (T : array int) (a b : int) : Z := (φ (T.[a * n + b])).
Definition vtx (a : int) : N := Z.to_N ((φ a) + 1).

Lemma idx_val : forall a b, inr a -> inr b -> (φ (a * n + b)) = ((φ a) * (φ n) + (φ b))%Z.
Proof.
  unfold inr. intros a b Ha Hb.
  pose proof (to_Z_bounded a). pose proof (to_Z_bounded b).
  assert ((φ a) * (φ n) <= 499 * 500)%Z by nia.
  rewrite add_spec, mul_spec. rewrite (Z.mod_small ((φ a) * (φ n))) by lia.
  apply Z.mod_small. lia.
Qed.

Lemma pos_inj : forall a b c d, inr a -> inr b -> inr c -> inr d ->
  ((φ a) * (φ n) + (φ b) = (φ c) * (φ n) + (φ d))%Z -> a = c /\ b = d.
Proof.
  unfold inr. intros a b c d Ha Hb Hc Hd E.
  pose proof (to_Z_bounded a). pose proof (to_Z_bounded b).
  pose proof (to_Z_bounded c). pose proof (to_Z_bounded d).
  assert ((φ a) = (φ c)).
  { destruct (Z.lt_trichotomy (φ a) (φ c)) as [L | [L | L]]; [| exact L |]; nia. }
  split; apply to_Z_inj; lia.
Qed.

Lemma idx_lt : forall a b, inr a -> inr b -> ((φ (a * n + b)) < (φ n) * (φ n))%Z.
Proof.
  intros a b Ha Hb. rewrite idx_val by assumption. unfold inr in *. nia.
Qed.

Lemma C_setmin : forall T a b c d s,
  (φ (PArray.length T)) = ((φ n) * (φ n))%Z ->
  inr a -> inr b -> inr c -> inr d ->
  C (setmin T (a * n + b) s) c d =
  if ((a =? c) && (b =? d))%bool then Z.min (C T a b) (φ s) else C T c d.
Proof.
  intros T a b c d s HL Ha Hb Hc Hd. unfold C.
  rewrite setmin_get by (rewrite HL; apply idx_lt; assumption).
  destruct (eqbP (a * n + b) (c * n + d)) as [E | E].
  - assert ((φ (a * n + b)) = (φ (c * n + d))) as E' by (rewrite E; reflexivity).
    rewrite !idx_val in E' by assumption.
    destruct (pos_inj a b c d Ha Hb Hc Hd E') as [-> ->].
    rewrite !eqb_refl. reflexivity.
  - destruct (eqbP a c), (eqbP b d); try reflexivity.
    subst. contradiction.
Qed.

Lemma C_setmin_len : forall T p s,
  PArray.length (setmin T p s) = PArray.length T.
Proof. exact setmin_len. Qed.

Record fwinv (K : Z) (T : array int) : Prop := {
  fi_len : (φ (PArray.length T)) = ((φ n) * (φ n))%Z;
  fi_bnd : forall a b, inr a -> inr b -> (C T a b <= (φ INF))%Z;
  fi_diag : forall a, inr a -> C T a a = 0%Z;
  fi_walk : forall a b, inr a -> inr b -> (C T a b < (φ INF))%Z ->
    walk ri rj rk (vtx a) (vtx b) (Z.to_N (C T a b));
  fi_road : forall a b k, inr a -> inr b -> road ri rj rk (vtx a) (vtx b) k ->
    (C T a b <= Z.of_N k)%Z;
  fi_tri : forall a b c, inr a -> inr b -> inr c -> ((φ c) < K)%Z ->
    (C T a b <= C T a c + C T c b)%Z
}.

Lemma C_nonneg : forall T a b, (0 <= C T a b)%Z.
Proof. intros. unfold C. apply to_Z_bounded. Qed.

Lemma walk_app : forall u v w L1 L2,
  walk ri rj rk u v L1 -> walk ri rj rk v w L2 -> walk ri rj rk u w (L1 + L2).
Proof.
  intros u v w L1 L2 H1. revert L2. induction H1 as [u | u v' w' k L H HW IH];
    intros L2 H2.
  - exact H2.
  - rewrite <- N.add_assoc. econstructor; [exact H | apply IH; exact H2].
Qed.

Definition newc (T0 : array int) (k a b : int) : Z :=
  Z.min (C T0 a b) (C T0 a k + C T0 k b).

Definition stepped (T0 : array int) (k : int) (T : array int) (q : Z) : Prop :=
  (φ (PArray.length T)) = ((φ n) * (φ n))%Z /\
  forall a b, inr a -> inr b ->
    C T a b = if ((φ a) * (φ n) + (φ b) <? q)%Z then newc T0 k a b else C T0 a b.

Lemma newc_k : forall K T0 k a, fwinv K T0 -> inr k -> inr a ->
  newc T0 k k a = C T0 k a /\ newc T0 k a k = C T0 a k.
Proof.
  intros K T0 k a HI Hk Ha. unfold newc.
  rewrite (fi_diag _ _ HI k Hk).
  pose proof (C_nonneg T0 k a). pose proof (C_nonneg T0 a k). lia.
Qed.

Lemma stepped_k : forall K T0 k T q a, fwinv K T0 -> inr k -> inr a ->
  stepped T0 k T q -> C T k a = C T0 k a /\ C T a k = C T0 a k.
Proof.
  intros K T0 k T q a HI Hk Ha [_ HS].
  destruct (newc_k K T0 k a HI Hk Ha) as [E1 E2].
  rewrite (HS k a Hk Ha), (HS a k Ha Hk).
  destruct (_ <? q)%Z, (_ <? q)%Z; lia.
Qed.

Lemma fw_j_spec : forall K T0 k i, fwinv K T0 -> inr k -> inr i ->
  forall aik, (φ aik) = C T0 i k ->
  forall z j T H, gap n j = z -> ((φ j) <= (φ n))%Z ->
  stepped T0 k T ((φ i) * (φ n) + (φ j)) ->
  stepped T0 k (fw_j n (i * n) (k * n) aik j T H) ((φ i) * (φ n) + (φ n)).
Proof.
  intros K T0 k i HI Hk Hi aik Haik z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j T H Hz Hj HS. destruct H as [HA]. simpl.
  destruct (bdec (j <? n)) as [Hjn | Hjn].
  - pose proof Hjn as Hj'. rewrite ltb_spec in Hj'.
    assert (Hj1 : (φ (j + 1)) = ((φ j) + 1)%Z) by sia.
    assert (Hjr : inr j) by exact Hj'.
    destruct (stepped_k K T0 k T _ j HI Hk Hjr HS) as [Ekj _].
    pose proof (fi_bnd _ _ HI i k Hi Hk). pose proof (fi_bnd _ _ HI k j Hk Hjr).
    pose proof (C_nonneg T0 i k). pose proof (C_nonneg T0 k j).
    assert (Hs : (φ (aik + T.[k * n + j])) = (C T0 i k + C T0 k j)%Z).
    { rewrite add_spec. change (φ (T.[k * n + j])) with (C T k j). rewrite Ekj, Haik. rewrite INF_val in *.
      apply Z.mod_small. lia. }
    destruct HS as [HL HS].
    eapply IH; [ | reflexivity | lia | ].
    + rewrite <- Hz. apply dec_step. exact Hjn.
    + split; [rewrite setmin_len; exact HL|].
      intros a b Ha Hb. rewrite (C_setmin T i j a b _ HL Hi Hjr Ha Hb).
      destruct (eqbP i a) as [<- | Ea]; destruct (eqbP j b) as [<- | Eb];
        simpl.
      * rewrite (HS i j Hi Hjr), Hs, Hj1.
        destruct (Z.ltb_spec ((φ i) * (φ n) + (φ j)) ((φ i) * (φ n) + (φ j))); [lia|].
        destruct (Z.ltb_spec ((φ i) * (φ n) + (φ j)) ((φ i) * (φ n) + ((φ j) + 1))); [|lia].
        reflexivity.
      * rewrite (HS i b Hi Hb). rewrite Hj1.
        destruct (Z.ltb_spec ((φ i) * (φ n) + (φ b)) ((φ i) * (φ n) + (φ j)));
        destruct (Z.ltb_spec ((φ i) * (φ n) + (φ b)) ((φ i) * (φ n) + ((φ j) + 1)));
          try reflexivity; exfalso; apply Eb; apply to_Z_inj; lia.
      * rewrite (HS a j Ha Hjr). rewrite Hj1.
        destruct (Z.ltb_spec ((φ a) * (φ n) + (φ j)) ((φ i) * (φ n) + (φ j)));
        destruct (Z.ltb_spec ((φ a) * (φ n) + (φ j)) ((φ i) * (φ n) + ((φ j) + 1)));
          try reflexivity; exfalso; apply Ea;
          destruct (pos_inj i j a j Hi Hjr Ha Hjr ltac:(lia)); auto.
      * rewrite (HS a b Ha Hb). rewrite Hj1.
        destruct (Z.ltb_spec ((φ a) * (φ n) + (φ b)) ((φ i) * (φ n) + (φ j)));
        destruct (Z.ltb_spec ((φ a) * (φ n) + (φ b)) ((φ i) * (φ n) + ((φ j) + 1)));
          try reflexivity; exfalso; apply Ea;
          destruct (pos_inj i j a b Hi Hjr Ha Hb ltac:(lia)); auto.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hjn.
    replace ((φ i) * (φ n) + (φ n))%Z with ((φ i) * (φ n) + (φ j))%Z by lia. exact HS.
Qed.

Lemma fw_i_spec : forall K T0 k, fwinv K T0 -> inr k ->
  forall z i T H, gap n i = z -> ((φ i) <= (φ n))%Z ->
  stepped T0 k T ((φ i) * (φ n)) ->
  stepped T0 k (fw_i n k (k * n) i T H) ((φ n) * (φ n)).
Proof.
  intros K T0 k HI Hk z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i T H Hz Hi HS. destruct H as [HA]. simpl.
  destruct (bdec (i <? n)) as [Hin | Hin].
  - pose proof Hin as Hi'. rewrite ltb_spec in Hi'.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    assert (Hir : inr i) by exact Hi'.
    destruct (stepped_k K T0 k T _ i HI Hk Hir HS) as [_ Eik].
    eapply IH; [ | reflexivity | lia | ].
    + rewrite <- Hz. apply dec_step. exact Hin.
    + rewrite Hi1. replace (((φ i) + 1) * (φ n))%Z with ((φ i) * (φ n) + (φ n))%Z by ring.
      eapply fw_j_spec; [exact HI | exact Hk | exact Hir | | reflexivity | | ].
      * exact Eik.
      * change (φ 0) with 0%Z. lia.
      * change (φ 0) with 0%Z. rewrite Z.add_0_r. exact HS.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hin.
    replace ((φ n) * (φ n))%Z with ((φ i) * (φ n))%Z by (f_equal; lia). exact HS.
Qed.

Lemma fw_step_inv : forall T0 k T1, fwinv (φ k) T0 -> inr k ->
  stepped T0 k T1 ((φ n) * (φ n)) -> fwinv ((φ k) + 1) T1.
Proof.
  intros T0 k T1 HI Hk [HL HS].
  assert (E : forall a b, inr a -> inr b -> C T1 a b = newc T0 k a b).
  { intros a b Ha Hb. rewrite (HS a b Ha Hb). unfold inr in *.
    destruct (Z.ltb_spec ((φ a) * (φ n) + (φ b)) ((φ n) * (φ n))); [reflexivity|].
    pose proof (to_Z_bounded a). pose proof (to_Z_bounded b). nia. }
  constructor.
  - exact HL.
  - intros a b Ha Hb. rewrite (E a b Ha Hb). unfold newc.
    pose proof (fi_bnd _ _ HI a b Ha Hb). lia.
  - intros a Ha. rewrite (E a a Ha Ha). unfold newc.
    rewrite (fi_diag _ _ HI a Ha).
    pose proof (C_nonneg T0 a k). pose proof (C_nonneg T0 k a). lia.
  - intros a b Ha Hb Hlt. rewrite (E a b Ha Hb) in *. unfold newc in *.
    pose proof (C_nonneg T0 a k). pose proof (C_nonneg T0 k b).
    destruct (Z.min_spec (C T0 a b) (C T0 a k + C T0 k b)) as [[_ M] | [_ M]];
      rewrite M in *.
    + apply (fi_walk _ _ HI a b Ha Hb Hlt).
    + rewrite Z2N.inj_add by assumption.
      apply walk_app with (vtx k).
      * apply (fi_walk _ _ HI a k Ha Hk). lia.
      * apply (fi_walk _ _ HI k b Hk Hb). lia.
  - intros a b r Ha Hb Hr. rewrite (E a b Ha Hb). unfold newc.
    pose proof (fi_road _ _ HI a b r Ha Hb Hr). lia.
  - intros a b c Ha Hb Hc Hck.
    rewrite (E a b Ha Hb), (E a c Ha Hc), (E c b Hc Hb). unfold newc.
    pose proof (C_nonneg T0 a k). pose proof (C_nonneg T0 k b).
    pose proof (C_nonneg T0 a c). pose proof (C_nonneg T0 c b).
    pose proof (C_nonneg T0 k c). pose proof (C_nonneg T0 c k).
    destruct (Z.eq_dec (φ c) (φ k)) as [Ec | Ec].
    + assert (c = k) by (apply to_Z_inj; exact Ec). subst c.
      rewrite (fi_diag _ _ HI k Hk). lia.
    + pose proof (fi_tri _ _ HI a b c Ha Hb Hc ltac:(lia)).
      pose proof (fi_tri _ _ HI k b c Hk Hb Hc ltac:(lia)).
      pose proof (fi_tri _ _ HI a k c Ha Hk Hc ltac:(lia)).
      lia.
Qed.

Lemma fw_k_spec : forall z k T H, gap n k = z -> ((φ k) <= (φ n))%Z ->
  fwinv (φ k) T -> fwinv (φ n) (fw_k n k T H).
Proof.
  intros z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k T H Hz Hk HI. destruct H as [HA]. simpl.
  destruct (bdec (k <? n)) as [Hkn | Hkn].
  - pose proof Hkn as Hk'. rewrite ltb_spec in Hk'.
    assert (Hk1 : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
    assert (Hkr : inr k) by exact Hk'.
    eapply IH; [ | reflexivity | lia | ].
    + rewrite <- Hz. apply dec_step. exact Hkn.
    + rewrite Hk1. apply fw_step_inv with T; [exact HI | exact Hkr|].
      eapply fw_i_spec; [exact HI | exact Hkr | reflexivity | |].
      * change (φ 0) with 0%Z. lia.
      * change (φ 0) with 0%Z. split; [exact (fi_len _ _ HI)|].
        intros a b Ha Hb. pose proof (to_Z_bounded a). pose proof (to_Z_bounded b).
        destruct (Z.ltb_spec ((φ a) * (φ n) + (φ b)) (0 * (φ n))); [nia | reflexivity].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hkn.
    replace (φ n) with (φ k) by lia. exact HI.
Qed.

Lemma fw_lower : forall T, fwinv (φ n) T ->
  (forall u v k, road ri rj rk u v k -> (1 <= Z.of_N v <= (φ n))%Z) ->
  forall u v L, walk ri rj rk u v L ->
  forall a, inr a -> u = vtx a ->
  exists b, inr b /\ v = vtx b /\ (C T a b <= Z.of_N L)%Z.
Proof.
  intros T HI Hrange u v L HW.
  induction HW as [u | u v w k L Hr HW IH]; intros a Ha Hu.
  - exists a. split; [exact Ha|]. split; [exact Hu|].
    rewrite (fi_diag _ _ HI a Ha). lia.
  - pose proof (Hrange _ _ _ Hr) as Hv.
    set (c := of_Z (Z.of_N v - 1)).
    assert (Hc : (φ c) = (Z.of_N v - 1)%Z).
    { unfold c. rewrite of_Z_spec. apply Z.mod_small.
      assert (wB = 9223372036854775808%Z) by reflexivity. lia. }
    assert (Hcr : inr c) by (unfold inr; lia).
    assert (Hvc : v = vtx c) by (unfold vtx; rewrite Hc; lia).
    destruct (IH c Hcr Hvc) as (b & Hb & Hwb & Hcb).
    exists b. split; [exact Hb|]. split; [exact Hwb|].
    subst u. rewrite Hvc in Hr.
    pose proof (fi_road _ _ HI a c k Ha Hcr Hr).
    pose proof (fi_tri _ _ HI a b c Ha Hb Hcr Hcr).
    lia.
Qed.

End FW.

Lemma road_sym : forall ri rj rk u v k,
  road ri rj rk u v k -> road ri rj rk v u k.
Proof.
  intros ri rj rk u v k (e & He & Hk & Huv). exists e. split; [exact He|].
  split; [exact Hk|]. tauto.
Qed.

Lemma walk_one : forall ri rj rk u v k,
  road ri rj rk u v k -> walk ri rj rk u v k.
Proof.
  intros ri rj rk u v k H. rewrite <- (N.add_0_r k).
  econstructor; [exact H | constructor].
Qed.

Section Init.

Variable n : int.
Hypothesis Hn : (2 <= (φ n) <= 500)%Z.
Variables ri rj rk : list N.

Record base (T : array int) : Prop := {
  ba_len : (φ (PArray.length T)) = ((φ n) * (φ n))%Z;
  ba_bnd : forall a b, inr n a -> inr n b -> (C n T a b <= (φ INF))%Z;
  ba_diag : forall a, inr n a -> C n T a a = 0%Z;
  ba_walk : forall a b, inr n a -> inr n b -> (C n T a b < (φ INF))%Z ->
    walk ri rj rk (vtx a) (vtx b) (Z.to_N (C n T a b))
}.

Lemma base_setmin : forall T u v s, base T -> inr n u -> inr n v ->
  walk ri rj rk (vtx u) (vtx v) (Z.to_N (φ s)) ->
  base (setmin T (u * n + v) s) /\
  (forall a b, inr n a -> inr n b -> (C n (setmin T (u * n + v) s) a b <= C n T a b)%Z) /\
  (C n (setmin T (u * n + v) s) u v <= (φ s))%Z.
Proof.
  intros T u v s HB Hu Hv HW.
  pose proof (ba_len _ HB) as HL.
  assert (E : forall a b, inr n a -> inr n b ->
    C n (setmin T (u * n + v) s) a b =
    if ((u =? a) && (v =? b))%bool then Z.min (C n T u v) (φ s) else C n T a b)
    by (intros; apply C_setmin; assumption).
  split; [|split].
  - constructor.
    + rewrite setmin_len. exact HL.
    + intros a b Ha Hb. rewrite (E a b Ha Hb).
      destruct (eqbP u a); destruct (eqbP v b); simpl; subst;
        pose proof (ba_bnd _ HB a b Ha Hb); lia.
    + intros a Ha. rewrite (E a a Ha Ha).
      destruct (eqbP u a); destruct (eqbP v a); simpl; subst;
        try apply (ba_diag _ HB); try assumption.
      rewrite (ba_diag _ HB a Ha). pose proof (to_Z_bounded s). lia.
    + intros a b Ha Hb. rewrite (E a b Ha Hb).
      destruct (eqbP u a); destruct (eqbP v b); simpl; subst;
        try apply (ba_walk _ HB); try assumption.
      intros Hlt. destruct (Z.min_spec (C n T a b) (φ s)) as [[_ M] | [_ M]];
        rewrite M in *; [apply (ba_walk _ HB); assumption | exact HW].
  - intros a b Ha Hb. rewrite (E a b Ha Hb).
    destruct (eqbP u a); destruct (eqbP v b); simpl; subst; lia.
  - rewrite (E u v Hu Hv). rewrite !eqb_refl. simpl. lia.
Qed.

Lemma C_set : forall T a b c d s,
  (φ (PArray.length T)) = ((φ n) * (φ n))%Z ->
  inr n a -> inr n b -> inr n c -> inr n d ->
  C n (T.[a * n + b <- s]) c d =
  if ((a =? c) && (b =? d))%bool then (φ s) else C n T c d.
Proof.
  intros T a b c d s HL Ha Hb Hc Hd. unfold C.
  destruct (eqbP (a * n + b) (c * n + d)) as [E | E].
  - rewrite <- E. rewrite aget_set_same
      by (rewrite ltb_spec, HL; apply idx_lt; assumption).
    assert ((φ (a * n + b)) = (φ (c * n + d))) as E' by (rewrite E; reflexivity).
    rewrite !idx_val in E' by assumption.
    destruct (pos_inj n Hn a b c d Ha Hb Hc Hd E') as [-> ->].
    rewrite !eqb_refl. reflexivity.
  - rewrite aget_set_other by exact E.
    destruct (eqbP a c), (eqbP b d); try reflexivity.
    subst. contradiction.
Qed.

Definition dinv (i : int) (T : array int) : Prop :=
  (φ (PArray.length T)) = ((φ n) * (φ n))%Z /\
  forall a b, inr n a -> inr n b ->
    C n T a b = if (((φ a) =? (φ b))%Z && ((φ a) <? (φ i))%Z)%bool then 0%Z else (φ INF).

Lemma diag_spec : forall z i T H, gap n i = z -> ((φ i) <= (φ n))%Z ->
  dinv i T -> dinv n (diag_loop n i T H).
Proof.
  intros z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i T H Hz Hi [HL HD]. destruct H as [HA]. simpl.
  destruct (bdec (i <? n)) as [Hin | Hin].
  - pose proof Hin as Hi'. rewrite ltb_spec in Hi'.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    assert (Hir : inr n i) by exact Hi'.
    eapply IH; [ | reflexivity | lia | ].
    + rewrite <- Hz. apply dec_step. exact Hin.
    + split; [rewrite alength_set; exact HL|].
      intros a b Ha Hb. rewrite (C_set T i i a b 0 HL Hir Hir Ha Hb), Hi1.
      destruct (eqbP i a) as [Ea|Ea]; destruct (eqbP i b) as [Eb|Eb]; simpl.
      * subst a b. rewrite Z.eqb_refl. simpl.
        rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
      * rewrite (HD a b Ha Hb). subst a.
        destruct (Z.eqb_spec (φ i) (φ b)) as [E|E];
          [exfalso; apply Eb; apply to_Z_inj; exact E | reflexivity].
      * rewrite (HD a b Ha Hb). subst b.
        destruct (Z.eqb_spec (φ a) (φ i)) as [E|E];
          [exfalso; apply Ea; apply to_Z_inj; symmetry; exact E | reflexivity].
      * rewrite (HD a b Ha Hb).
        destruct (Z.eqb_spec (φ a) (φ b)); [|reflexivity]. simpl.
        destruct (Z.ltb_spec (φ a) (φ i)); destruct (Z.ltb_spec (φ a) ((φ i) + 1));
          try reflexivity; try lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hin.
    split; [exact HL|]. intros a b Ha Hb. rewrite (HD a b Ha Hb).
    replace (φ i) with (φ n) by lia. reflexivity.
Qed.

Lemma dinv_base : forall T, dinv n T -> base T.
Proof.
  intros T [HL HD]. constructor.
  - exact HL.
  - intros a b Ha Hb. rewrite (HD a b Ha Hb).
    destruct (_ && _)%bool; rewrite ?INF_val; lia.
  - intros a Ha. rewrite (HD a a Ha Ha). rewrite Z.eqb_refl.
    unfold inr in Ha. destruct (Z.ltb_spec (φ a) (φ n)); [reflexivity | lia].
  - intros a b Ha Hb. rewrite (HD a b Ha Hb).
    destruct (Z.eqb_spec (φ a) (φ b)) as [E|E]; simpl.
    + destruct (_ <? _)%Z; intros Hlt; [| lia].
      assert (a = b) by (apply to_Z_inj; exact E). subst. constructor.
    + intros Hlt; lia.
Qed.

Variables (xi xj xk : array int) (m : int).
Hypothesis Hedge : forall e, ((φ e) < (φ m))%Z ->
  (1 <= (φ (xi.[e])) <= (φ n))%Z /\ (1 <= (φ (xj.[e])) <= (φ n))%Z /\
  road ri rj rk (Z.to_N (φ (xi.[e]))) (Z.to_N (φ (xj.[e]))) (Z.to_N (φ (xk.[e]))).

Definition einv (e : int) (T : array int) : Prop :=
  base T /\ forall e', ((φ e') < (φ e))%Z ->
    (C n T (xi.[e'] - 1) (xj.[e'] - 1) <= (φ (xk.[e'])))%Z /\
    (C n T (xj.[e'] - 1) (xi.[e'] - 1) <= (φ (xk.[e'])))%Z.

Lemma edge_spec : forall z e T H, gap m e = z -> ((φ e) <= (φ m))%Z ->
  einv e T -> einv m (edge_loop n xi xj xk m e T H).
Proof.
  intros z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros e T H Hz He [HB HE]. destruct H as [HA]. simpl.
  destruct (bdec (e <? m)) as [Hem | Hem].
  - pose proof Hem as He'. rewrite ltb_spec in He'.
    assert (He1 : (φ (e + 1)) = ((φ e) + 1)%Z) by sia.
    destruct (Hedge e He') as (Hi & Hj & Hr).
    assert (Hu : (φ (xi.[e] - 1)) = ((φ (xi.[e])) - 1)%Z) by (apply sub1_val; lia).
    assert (Hv : (φ (xj.[e] - 1)) = ((φ (xj.[e])) - 1)%Z) by (apply sub1_val; lia).
    set (u := xi.[e] - 1) in *. set (v := xj.[e] - 1) in *.
    assert (Hur : inr n u) by (unfold inr; lia).
    assert (Hvr : inr n v) by (unfold inr; lia).
    assert (Vu : vtx u = Z.to_N (φ (xi.[e]))) by (unfold vtx; rewrite Hu; f_equal; lia).
    assert (Vv : vtx v = Z.to_N (φ (xj.[e]))) by (unfold vtx; rewrite Hv; f_equal; lia).
    destruct (base_setmin T u v (xk.[e]) HB Hur Hvr)
      as (HB1 & Hm1 & Hc1).
    { rewrite Vu, Vv. apply walk_one. exact Hr. }
    destruct (base_setmin (setmin T (u * n + v) xk.[e]) v u (xk.[e]) HB1 Hvr Hur)
      as (HB2 & Hm2 & Hc2).
    { rewrite Vu, Vv. apply walk_one. apply road_sym. exact Hr. }
    eapply IH; [ | reflexivity | lia | ].
    + rewrite <- Hz. apply dec_step. exact Hem.
    + split; [exact HB2|].
      intros e' He''. rewrite He1 in He''.
      destruct (Z.eq_dec (φ e') (φ e)) as [Ee | Ee].
      * assert (e' = e) by (apply to_Z_inj; exact Ee). subst e'. fold u v.
        pose proof (Hm2 u v Hur Hvr). split; lia.
      * destruct (HE e' ltac:(lia)) as [H1 H2].
        destruct (Hedge e' ltac:(lia)) as (Hi' & Hj' & _).
        assert (inr n (xi.[e'] - 1)) by (unfold inr; rewrite sub1_val; lia).
        assert (inr n (xj.[e'] - 1)) by (unfold inr; rewrite sub1_val; lia).
        pose proof (Hm1 (xi.[e'] - 1) (xj.[e'] - 1) ltac:(assumption) ltac:(assumption)).
        pose proof (Hm2 (xi.[e'] - 1) (xj.[e'] - 1) ltac:(assumption) ltac:(assumption)).
        pose proof (Hm1 (xj.[e'] - 1) (xi.[e'] - 1) ltac:(assumption) ltac:(assumption)).
        pose proof (Hm2 (xj.[e'] - 1) (xi.[e'] - 1) ltac:(assumption) ltac:(assumption)).
        split; lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hem.
    replace m with e by (apply to_Z_inj; lia). split; assumption.
Qed.

Hypothesis Hroad : forall u v k, road ri rj rk u v k -> exists e, ((φ e) < (φ m))%Z /\
  Z.of_N k = (φ (xk.[e])) /\
  ((Z.of_N u = (φ (xi.[e])) /\ Z.of_N v = (φ (xj.[e]))) \/
   (Z.of_N u = (φ (xj.[e])) /\ Z.of_N v = (φ (xi.[e])))).

Lemma einv_fwinv : forall T, einv m T -> fwinv n ri rj rk 0 T.
Proof.
  intros T [HB HE]. constructor.
  - exact (ba_len _ HB).
  - exact (ba_bnd _ HB).
  - exact (ba_diag _ HB).
  - exact (ba_walk _ HB).
  - intros a b k Ha Hb Hr.
    destruct (Hroad _ _ _ Hr) as (e & He & Hk & Hab).
    destruct (Hedge e He) as (Hi & Hj & _).
    destruct (HE e He) as [H1 H2].
    unfold vtx in Hab. unfold inr in Ha, Hb.
    pose proof (to_Z_bounded a). pose proof (to_Z_bounded b).
    destruct Hab as [[Ea Eb] | [Ea Eb]].
    + assert (a = xi.[e] - 1) by (apply to_Z_inj; rewrite sub1_val; lia).
      assert (b = xj.[e] - 1) by (apply to_Z_inj; rewrite sub1_val; lia).
      subst a b. lia.
    + assert (a = xj.[e] - 1) by (apply to_Z_inj; rewrite sub1_val; lia).
      assert (b = xi.[e] - 1) by (apply to_Z_inj; rewrite sub1_val; lia).
      subst a b. lia.
  - intros a b c _ _ _ Hc. pose proof (to_Z_bounded c). lia.
Qed.

End Init.

(* ------------------------------------------------------------------ *)
(* Dijkstra                                                            *)
(* ------------------------------------------------------------------ *)

(* the number of unvisited cells among 0 .. k-1 (proof side only) *)
Fixpoint ucnt (vis : array bool) (k : nat) : nat :=
  match k with
  | O => O
  | S k' => (ucnt vis k' + (if vis.[of_Z (Z.of_nat k')] then 0 else 1))%nat
  end.

Lemma ofnat_val : forall k : nat, (Z.of_nat k < 4194304)%Z ->
  (φ (of_Z (Z.of_nat k))) = Z.of_nat k.
Proof.
  intros k Hk. rewrite of_Z_spec. apply Z.mod_small.
  assert (wB = 9223372036854775808%Z) by reflexivity. lia.
Qed.

Lemma ucnt_set : forall vis u, (u <? PArray.length vis) = true -> vis.[u] = false ->
  forall k : nat, (Z.of_nat k < 4194304)%Z ->
  (ucnt (vis.[u <- true]) k + (if ((φ u) <? Z.of_nat k)%Z then 1 else 0) = ucnt vis k)%nat.
Proof.
  intros vis u Hu Hf k. induction k as [| k IH]; intros Hk.
  - simpl. pose proof (to_Z_bounded u). destruct (Z.ltb_spec (φ u) 0); [lia | reflexivity].
  - cbn [ucnt]. specialize (IH ltac:(lia)).
    pose proof (ofnat_val k ltac:(lia)) as Ek.
    destruct (eqbP u (of_Z (Z.of_nat k))) as [E | E].
    + rewrite <- E. rewrite bget_set_same by exact Hu. rewrite Hf.
      assert ((φ u) = Z.of_nat k) by (rewrite E; exact Ek).
      destruct (Z.ltb_spec (φ u) (Z.of_nat k)); [lia|].
      destruct (Z.ltb_spec (φ u) (Z.of_nat (S k))); [|lia]. lia.
    + rewrite bget_set_other by exact E.
      assert ((φ u) <> Z.of_nat k) by (intro F; apply E; apply to_Z_inj; lia).
      destruct (Z.ltb_spec (φ u) (Z.of_nat k));
        destruct (Z.ltb_spec (φ u) (Z.of_nat (S k))); try lia.
Qed.

Lemma ucnt_pos : forall vis u, vis.[u] = false ->
  forall k : nat, (Z.of_nat k < 4194304)%Z -> ((φ u) < Z.of_nat k)%Z ->
  (0 < ucnt vis k)%nat.
Proof.
  intros vis u Hf k. induction k as [| k IH]; intros Hk Hu.
  - lia.
  - simpl. destruct (Z.eq_dec (φ u) (Z.of_nat k)) as [E | E].
    + assert (u = of_Z (Z.of_nat k)) by (apply to_Z_inj; rewrite ofnat_val by lia; exact E).
      subst u. rewrite Hf. lia.
    + specialize (IH ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma ucnt_make : forall M k, ucnt (PArray.make M false) k = k.
Proof.
  intros M k. induction k as [| k IH]; [reflexivity|].
  simpl. rewrite IH, bget_make. lia.
Qed.

Section Dij.

Variables (n M tgt d : int) (V T : array int) (w : int -> int -> Z).
Hypothesis HM : (2 <= (φ M) <= 501)%Z.
Hypothesis Htgt : (0 < (φ tgt) < (φ M))%Z.
Hypothesis Hd : ((φ d) < 2147483648)%Z.
Hypothesis Hw : forall a b, (0 <= w a b)%Z.
Hypothesis Hwdef : forall a b, ((φ a) < (φ M))%Z -> ((φ b) < (φ M))%Z ->
  (φ (T.[V.[a] * n + V.[b]])) = w a b.

Inductive dp : int -> Z -> Prop :=
  | dp_src : dp 0 0
  | dp_step : forall a b L, dp a L -> a <> tgt -> ((φ b) < (φ M))%Z ->
      (w a b <= (φ d))%Z -> dp b (L + w a b).

Lemma dp_range : forall a L, dp a L -> ((φ a) < (φ M))%Z /\ (0 <= L)%Z.
Proof.
  intros a L H. induction H as [| a b L H IH Ha Hb Hw'].
  - change (φ 0) with 0%Z. lia.
  - pose proof (Hw a b). lia.
Qed.

Record dji (vis : array bool) (dist : array int) : Prop := {
  dj_lv : (φ (PArray.length vis)) = (φ M);
  dj_ld : (φ (PArray.length dist)) = (φ M);
  dj_bnd : forall a, ((φ a) < (φ M))%Z -> ((φ (dist.[a])) <= (φ INF))%Z;
  dj_src : (φ (dist.[0])) = 0%Z;
  dj_d1 : forall a, ((φ a) < (φ M))%Z -> ((φ (dist.[a])) < (φ INF))%Z -> dp a (φ (dist.[a]));
  dj_d2 : forall a, ((φ a) < (φ M))%Z -> vis.[a] = true ->
    forall L, dp a L -> ((φ (dist.[a])) <= L)%Z;
  dj_d3 : forall a b, ((φ a) < (φ M))%Z -> ((φ b) < (φ M))%Z -> vis.[a] = true -> vis.[b] = false ->
    a <> tgt -> (w a b <= (φ d))%Z -> ((φ (dist.[b])) <= (φ (dist.[a])) + w a b)%Z;
  dj_tgt : vis.[tgt] = false
}.

Lemma cut : forall vis dist, dji vis dist -> forall a L, dp a L ->
  vis.[a] = true \/
  exists x, ((φ x) < (φ M))%Z /\ vis.[x] = false /\ ((φ (dist.[x])) <= L)%Z.
Proof.
  intros vis dist HI a L H.
  induction H as [| a b L H IH Ha Hb Hw'].
  - destruct (vis.[0]) eqn:E; [left; reflexivity|].
    right. exists 0. change (φ 0) with 0%Z. rewrite (dj_src _ _ HI). split; [lia|].
    split; [exact E | lia].
  - pose proof (dp_range a L H) as [Har HL]. pose proof (Hw a b).
    destruct IH as [Va | (x & Hx & Vx & Dx)].
    + destruct (vis.[b]) eqn:Vb; [left; reflexivity|].
      right. exists b. split; [exact Hb|]. split; [exact Vb|].
      pose proof (dj_d3 _ _ HI a b Har Hb Va Vb Ha Hw').
      pose proof (dj_d2 _ _ HI a Har Va L H). lia.
    + right. exists x. split; [exact Hx|]. split; [exact Vx | lia].
Qed.

(* the selection scan *)
Definition selr (vis : array bool) (dist : array int) (u : int) : Prop :=
  (u = M /\ forall x, ((φ x) < (φ M))%Z -> vis.[x] = false -> ((φ INF) <= (φ (dist.[x])))%Z) \/
  (((φ u) < (φ M))%Z /\ vis.[u] = false /\ ((φ (dist.[u])) < (φ INF))%Z /\
   forall x, ((φ x) < (φ M))%Z -> vis.[x] = false -> ((φ (dist.[u])) <= (φ (dist.[x])))%Z).

Lemma sel_spec : forall vis dist z i b bv H, gap M i = z -> ((φ i) <= (φ M))%Z ->
  ((b = M /\ bv = INF) \/
   (((φ b) < (φ M))%Z /\ vis.[b] = false /\ dist.[b] = bv /\ ((φ bv) < (φ INF))%Z)) ->
  (forall x, ((φ x) < (φ i))%Z -> vis.[x] = false -> ((φ bv) <= (φ (dist.[x])))%Z) ->
  selr vis dist (sel_loop M vis dist i b bv H).
Proof.
  intros vis dist z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i b bv H Hz Hi Hb Hx. destruct H as [HA]. simpl.
  destruct (bdec (i <? M)) as [Him | Him].
  - pose proof Him as Hi'. rewrite ltb_spec in Hi'.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    assert (Hdec : Zwf 0 (gap M (i + 1)) z) by (rewrite <- Hz; apply dec_step; exact Him).
    destruct (vis.[i]) eqn:Vi.
    + eapply IH; [exact Hdec | reflexivity | lia | exact Hb |].
      intros x Hx' Vx. rewrite Hi1 in Hx'.
      destruct (Z.eq_dec (φ x) (φ i)) as [E|E].
      * assert (x = i) by (apply to_Z_inj; exact E). subst. congruence.
      * apply Hx; [lia | exact Vx].
    + destruct (ltbP (dist.[i]) bv) as [Lt | Ge].
      * eapply IH; [exact Hdec | reflexivity | lia | |].
        -- right. split; [exact Hi'|]. split; [exact Vi|]. split; [reflexivity|].
           destruct Hb as [[_ ->] | (_ & _ & _ & Hbv)]; lia.
        -- intros x Hx' Vx. rewrite Hi1 in Hx'.
           destruct (Z.eq_dec (φ x) (φ i)) as [E|E].
           ++ assert (x = i) by (apply to_Z_inj; exact E). subst. lia.
           ++ pose proof (Hx x ltac:(lia) Vx). lia.
      * eapply IH; [exact Hdec | reflexivity | lia | exact Hb |].
        intros x Hx' Vx. rewrite Hi1 in Hx'.
        destruct (Z.eq_dec (φ x) (φ i)) as [E|E].
        -- assert (x = i) by (apply to_Z_inj; exact E). subst. lia.
        -- apply Hx; [lia | exact Vx].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Him.
    destruct Hb as [[-> ->] | (Hb & Vb & Db & Hbv)].
    + left. split; [reflexivity|]. intros x Hx' Vx. apply Hx; [lia | exact Vx].
    + right. split; [exact Hb|]. split; [exact Vb|]. rewrite Db. split; [exact Hbv|].
      intros x Hx' Vx. apply Hx; [lia | exact Vx].
Qed.

(* the relaxation *)
Definition fr (vis : array bool) (dist : array int) (u c : int) : Z :=
  if vis.[c] then (φ (dist.[c]))
  else if (w u c <=? (φ d))%Z then Z.min (φ (dist.[c])) ((φ (dist.[u])) + w u c)
  else (φ (dist.[c])).

Lemma rel_spec : forall vis dist u, ((φ u) < (φ M))%Z ->
  ((φ (dist.[u])) < (φ INF))%Z ->
  forall z b D H, gap M b = z -> ((φ b) <= (φ M))%Z ->
  (φ (PArray.length D)) = (φ M) ->
  (forall c, ((φ c) < (φ M))%Z ->
     (φ (D.[c])) = if ((φ c) <? (φ b))%Z then fr vis dist u c else (φ (dist.[c]))) ->
  (φ (PArray.length (rel_loop M V T vis d (V.[u] * n) dist.[u] b D H))) = (φ M) /\
  forall c, ((φ c) < (φ M))%Z ->
    (φ ((rel_loop M V T vis d (V.[u] * n) dist.[u] b D H).[c])) = fr vis dist u c.
Proof.
  intros vis dist u Hu Hdu z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros b D H Hz Hb HL HD. destruct H as [HA]. simpl.
  destruct (bdec (b <? M)) as [Hbm | Hbm].
  - pose proof Hbm as Hb'. rewrite ltb_spec in Hb'.
    assert (Hb1 : (φ (b + 1)) = ((φ b) + 1)%Z) by sia.
    assert (Hdec : Zwf 0 (gap M (b + 1)) z) by (rewrite <- Hz; apply dec_step; exact Hbm).
    assert (Hwb := Hwdef u b Hu Hb').
    set (D' := if vis.[b] then D else
                 if T.[V.[u] * n + V.[b]] <=? d
                 then setmin D b (dist.[u] + T.[V.[u] * n + V.[b]]) else D).
    assert (HL' : (φ (PArray.length D')) = (φ M)).
    { unfold D'. destruct (vis.[b]); [exact HL|].
      destruct (_ <=? d); [rewrite setmin_len|]; exact HL. }
    assert (HD' : forall c, ((φ c) < (φ M))%Z ->
       (φ (D'.[c])) = if ((φ c) <? (φ b) + 1)%Z then fr vis dist u c else (φ (dist.[c]))).
    { intros c Hc.
      destruct (Z.eq_dec (φ c) (φ b)) as [E|E].
      - assert (c = b) by (apply to_Z_inj; exact E). subst c.
        rewrite (proj2 (Z.ltb_lt _ _)) by lia.
        unfold D', fr. destruct (vis.[b]) eqn:Vb.
        + rewrite (HD b Hc). rewrite Z.ltb_irrefl. reflexivity.
        + destruct (lebP (T.[V.[u] * n + V.[b]]) d) as [Le | Gt];
            rewrite Hwb in *.
          * rewrite (proj2 (Z.leb_le _ _)) by exact Le.
            rewrite setmin_get by (rewrite HL; exact Hc). rewrite eqb_refl.
            rewrite (HD b Hc). rewrite Z.ltb_irrefl.
            f_equal. rewrite add_spec, Hwb. apply Z.mod_small.
            pose proof (to_Z_bounded (dist.[u])).
            assert (wB = 9223372036854775808%Z) by reflexivity.
            rewrite INF_val in Hdu. pose proof (Hw u b). lia.
          * rewrite (proj2 (Z.leb_gt _ _)) by lia.
            rewrite (HD b Hc). rewrite Z.ltb_irrefl. reflexivity.
      - assert (Ebc : b <> c) by (intro F; apply E; rewrite F; reflexivity).
        assert (D'.[c] = D.[c]) as ->.
        { unfold D'. destruct (vis.[b]); [reflexivity|].
          destruct (_ <=? d); [|reflexivity].
          unfold setmin. destruct (dist.[u] + T.[V.[u] * n + V.[b]] <? D.[b]); [|reflexivity].
          apply aget_set_other. exact Ebc. }
        rewrite (HD c Hc).
        destruct (Z.ltb_spec (φ c) (φ b)); destruct (Z.ltb_spec (φ c) ((φ b) + 1));
          try reflexivity; lia. }
    eapply IH; [exact Hdec | reflexivity | lia | exact HL' |].
    intros c Hc. rewrite Hb1. exact (HD' c Hc).
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hbm.
    split; [exact HL|]. intros c Hc. rewrite (HD c Hc).
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma dij_step_inv : forall vis dist u, dji vis dist -> ((φ u) < (φ M))%Z ->
  vis.[u] = false -> ((φ (dist.[u])) < (φ INF))%Z ->
  (forall x, ((φ x) < (φ M))%Z -> vis.[x] = false -> ((φ (dist.[u])) <= (φ (dist.[x])))%Z) ->
  u <> tgt ->
  dji (vis.[u <- true])
      (rel_loop M V T (vis.[u <- true]) d (V.[u] * n) dist.[u] 0 dist
         (Zwf_well_founded 0 (gap M 0))).
Proof.
  intros vis dist u HI Hu Vu Du Hmin Hut.
  set (vis' := vis.[u <- true]).
  destruct (rel_spec vis' dist u Hu Du _ 0 dist (Zwf_well_founded 0 (gap M 0))
              eq_refl ltac:(change (φ 0) with 0%Z; lia) (dj_ld _ _ HI))
    as [HRL HR].
  { intros c Hc. pose proof (to_Z_bounded c). change (φ 0) with 0%Z.
    destruct (Z.ltb_spec (φ c) 0); [lia | reflexivity]. }
  set (R := rel_loop M V T vis' d (V.[u] * n) dist.[u] 0 dist
              (Zwf_well_founded 0 (gap M 0))) in *.
  assert (Vu' : vis'.[u] = true).
  { unfold vis'. apply bget_set_same. rewrite ltb_spec, (dj_lv _ _ HI). exact Hu. }
  assert (Vo : forall c, c <> u -> vis'.[c] = vis.[c]).
  { intros c Hc. unfold vis'. apply bget_set_other. intro F; apply Hc; symmetry; exact F. }
  assert (D2u : forall L, dp u L -> ((φ (dist.[u])) <= L)%Z).
  { intros L HL. destruct (cut vis dist HI u L HL) as [V1 | (x & Hx & Vx & Dx)].
    - congruence.
    - pose proof (Hmin x Hx Vx). lia. }
  assert (frle : forall c, (fr vis' dist u c <= (φ (dist.[c])))%Z).
  { intros c. unfold fr. destruct (vis'.[c]); [lia|].
    destruct (_ <=? _)%Z; lia. }
  assert (frvis : forall c, vis'.[c] = true -> fr vis' dist u c = (φ (dist.[c]))).
  { intros c Vc. unfold fr. rewrite Vc. reflexivity. }
  assert (frcases : forall c, fr vis' dist u c = (φ (dist.[c])) \/
            (vis'.[c] = false /\ (w u c <= (φ d))%Z /\
             fr vis' dist u c = ((φ (dist.[u])) + w u c)%Z)).
  { intros c. unfold fr. destruct (vis'.[c]) eqn:Vc; [left; reflexivity|].
    destruct (Z.leb_spec (w u c) (φ d)); [|left; reflexivity].
    destruct (Z.min_spec (φ (dist.[c])) ((φ (dist.[u])) + w u c)) as [[_ ->] | [_ ->]];
      [left; reflexivity | right; auto]. }
  assert (HM0 : ((φ 0) < (φ M))%Z) by (change (φ 0) with 0%Z; lia).
  constructor.
  - unfold vis'. rewrite blength_set. exact (dj_lv _ _ HI).
  - exact HRL.
  - intros a Ha. rewrite (HR a Ha). pose proof (frle a). pose proof (dj_bnd _ _ HI a Ha). lia.
  - pose proof (HR 0 HM0) as E0. pose proof (frle 0). pose proof (to_Z_bounded (R.[0])).
    rewrite (dj_src _ _ HI) in *. lia.
  - intros a Ha Hlt. rewrite (HR a Ha) in *.
    destruct (frcases a) as [E | (Va & Hwa & E)]; rewrite E in *.
    + apply (dj_d1 _ _ HI a Ha Hlt).
    + apply dp_step; [ | exact Hut | exact Ha | exact Hwa].
      apply (dj_d1 _ _ HI u Hu Du).
  - intros a Ha Va' L HL. rewrite (HR a Ha), (frvis a Va').
    destruct (eqbP a u) as [Ea | Ea].
    + subst a. apply D2u. exact HL.
    + rewrite (Vo a Ea) in Va'. apply (dj_d2 _ _ HI a Ha Va' L HL).
  - intros a b Ha Hb Va' Vb' Hat Hwab. rewrite (HR a Ha), (HR b Hb), (frvis a Va').
    assert (Hbu : b <> u) by (intro F; subst b; congruence).
    assert (Vb : vis.[b] = false) by (rewrite <- (Vo b Hbu); exact Vb').
    destruct (eqbP a u) as [Ea | Ea].
    + subst a. unfold fr. rewrite Vb'.
      destruct (Z.leb_spec (w u b) (φ d)); [lia | lia].
    + rewrite (Vo a Ea) in Va'.
      pose proof (dj_d3 _ _ HI a b Ha Hb Va' Vb Hat Hwab). pose proof (frle b). lia.
  - rewrite (Vo tgt (fun F => Hut (eq_sym F))). exact (dj_tgt _ _ HI).
Qed.

Definition dij_res (o : option int) : Prop :=
  match o with
  | Some D => dp tgt (φ D) /\ forall L, dp tgt L -> ((φ D) <= L)%Z
  | None => forall L, dp tgt L -> ((φ INF) <= L)%Z
  end.

Lemma dij_spec : forall z r vis dist H, (φ r) = z -> dji vis dist ->
  ucnt vis (Z.to_nat (φ M)) = Z.to_nat (φ r) ->
  dij_res (dij_loop n M tgt V T d r vis dist H).
Proof.
  intros z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros r vis dist H Hz HI Hc. destruct H as [HA]. simpl.
  destruct (bdec (0 <? r)) as [Hr | Hr].
  - pose proof (sel_spec vis dist _ 0 M INF (Zwf_well_founded 0 (gap M 0)) eq_refl
                  ltac:(change (φ 0) with 0%Z; lia) (or_introl (conj eq_refl eq_refl))
                  ltac:(intros x Hx; pose proof (to_Z_bounded x);
                        change (φ 0) with 0%Z in Hx; lia)) as HS.
    set (u := sel_loop M vis dist 0 M INF (Zwf_well_founded 0 (gap M 0))) in *.
    destruct HS as [[Eu Hall] | (Hu & Vu & Du & Hmin)].
    + rewrite Eu, eqb_refl. intros L HL.
      destruct (cut vis dist HI tgt L HL) as [V1 | (x & Hx & Vx & Dx)].
      * rewrite (dj_tgt _ _ HI) in V1. discriminate.
      * pose proof (Hall x Hx Vx). lia.
    + assert (EuM : (u =? M) = false)
        by (apply eqb_false_spec; intro F; rewrite F in Hu; lia).
      rewrite EuM.
      destruct (eqbP u tgt) as [Et | Et].
      * split.
        -- rewrite <- Et. apply (dj_d1 _ _ HI u Hu Du).
        -- intros L HL. rewrite <- Et in HL.
           destruct (cut vis dist HI u L HL) as [V1 | (x & Hx & Vx & Dx)].
           ++ congruence.
           ++ pose proof (Hmin x Hx Vx). lia.
      * assert (Hr' : (0 < (φ r))%Z) by (rewrite ltb_spec in Hr; exact Hr).
        eapply IH; [ | reflexivity | |].
        -- rewrite <- Hz. apply dec_down. exact Hr.
        -- apply dij_step_inv; assumption.
        -- assert (Hlt : (u <? PArray.length vis) = true)
             by (rewrite ltb_spec, (dj_lv _ _ HI); exact Hu).
           pose proof (ucnt_set vis u Hlt Vu (Z.to_nat (φ M)) ltac:(lia)) as E.
           rewrite Z2Nat.id in E by lia.
           destruct (Z.ltb_spec (φ u) (φ M)); [|lia].
           assert ((φ (r - 1)) = ((φ r) - 1)%Z) by sia. lia.
  - exfalso. rewrite <- Bool.not_true_iff_false, ltb_spec in Hr.
    change (φ 0) with 0%Z in Hr.
    pose proof (ucnt_pos vis tgt (dj_tgt _ _ HI) (Z.to_nat (φ M)) ltac:(lia) ltac:(lia)).
    pose proof (to_Z_bounded r). lia.
Qed.

End Dij.

(* ------------------------------------------------------------------ *)
(* The intersections of the Dijkstra nodes                             *)
(* ------------------------------------------------------------------ *)

Definition vxinv (n : int) (xs : array int) (t i : int) (V : array int) : Prop :=
  (φ (PArray.length V)) = ((φ t) + 2)%Z /\ (φ (V.[0])) = 0%Z /\
  (φ (V.[t + 1])) = ((φ n) - 1)%Z /\
  forall a, (1 <= (φ a) <= (φ i))%Z -> (φ (V.[a])) = ((φ (xs.[a - 1])) - 1)%Z.

Lemma vx_spec : forall (n : int) (xs : array int) (t : int), ((φ t) < 500)%Z ->
  (forall i, ((φ i) < (φ t))%Z -> (1 <= (φ (xs.[i])))%Z) ->
  forall z i V H, gap t i = z -> ((φ i) <= (φ t))%Z ->
  vxinv n xs t i V -> vxinv n xs t t (vx_loop xs t i V H).
Proof.
  intros n xs t Ht Hxs z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i V H Hz Hi (HL & H0 & Ht1 & HV). destruct H as [HA]. simpl.
  destruct (bdec (i <? t)) as [Hit | Hit].
  - pose proof Hit as Hi'. rewrite ltb_spec in Hi'.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    assert (Ht1' : (φ (t + 1)) = ((φ t) + 1)%Z) by sia.
    assert (Hlt : (i + 1 <? PArray.length V) = true) by (rewrite ltb_spec; lia).
    eapply IH; [ | reflexivity | lia | ].
    + rewrite <- Hz. apply dec_step. exact Hit.
    + split; [rewrite alength_set; exact HL|].
      split; [rewrite aget_set_other; [exact H0 | intro F;
         assert ((φ (i + 1)) = (φ 0)) by (rewrite F; reflexivity);
         change (φ 0) with 0%Z in *; lia]|].
      split; [rewrite aget_set_other; [exact Ht1 | intro F;
         assert ((φ (i + 1)) = (φ (t + 1))) by (rewrite F; reflexivity); lia]|].
      intros a Ha. rewrite Hi1 in Ha.
      destruct (Z.eq_dec (φ a) ((φ i) + 1)) as [E | E].
      * assert (a = i + 1) by (apply to_Z_inj; lia). subst a.
        rewrite aget_set_same by exact Hlt.
        assert (i + 1 - 1 = i) as -> by (apply to_Z_inj; sia).
        apply sub1_val. apply Hxs. exact Hi'.
      * rewrite aget_set_other by (intro F; apply E; rewrite <- F; lia).
        apply HV. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hit.
    replace t with i at 4 by (apply to_Z_inj; lia).
    split; [exact HL|]. split; [exact H0|]. split; [exact Ht1|].
    intros a Ha. apply HV. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Reading the inputs                                                  *)
(* ------------------------------------------------------------------ *)

Lemma repr_len_u : forall (x : array@{Set} int) (l : list N),
  @repr (array uint) (list N) _ x l ->
  (φ (PArray.length@{Set} x)) = Z.of_nat (List.length l).
Proof. intros x l [Hl _]. symmetry. exact Hl. Qed.

Lemma repr_get_u : forall (x : array@{Set} int) (l : list N),
  @repr (array uint) (list N) _ x l ->
  forall i : int, ((φ i) < Z.of_nat (List.length l))%Z ->
  (φ (PArray.get@{Set} x i)) = Z.of_N (Prelude.get l (Z.to_N (φ i))).
Proof.
  intros x l [Hl Hc] i Hi.
  destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (m & Hm & Hr).
  unfold repr, repr_uint in Hr.
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded i); lia).
  rewrite of_to_Z in Hr.
  assert (E : Prelude.get l (Z.to_N (φ i)) = m).
  { unfold Prelude.get. rewrite Z_N_nat. apply nth_error_nth. exact Hm. }
  rewrite E, <- Hr. rewrite Z2N.id by apply to_Z_bounded. reflexivity.
Qed.

Lemma Forall2_nth' : forall {A B} (P : A -> B -> Prop) l1 l2 da db,
  Forall2 P l1 l2 -> forall k, (k < List.length l1)%nat -> P (nth k l1 da) (nth k l2 db).
Proof.
  intros A B P l1 l2 da db H. induction H as [| a b l1 l2 Hab H IH]; intros k Hk.
  - simpl in Hk. lia.
  - destruct k as [| k]; simpl; [exact Hab|]. apply IH. simpl in Hk. lia.
Qed.

Lemma dn_min : forall (P : N -> Prop) (k : N), P k ->
  ~ ~ exists D, P D /\ forall m, P m -> (D <= m)%N.
Proof.
  intros P k. induction k as [k IH] using (well_founded_ind N.lt_wf_0).
  intros Hk Hno. apply Hno. exists k. split; [exact Hk|].
  intros m Hm. destruct (N.lt_ge_cases m k) as [Lt | Ge]; [|exact Ge].
  exfalso. exact (IH m Lt Hm Hno).
Qed.

Lemma vtx_inj : forall a b, vtx a = vtx b -> a = b.
Proof.
  intros a b E. unfold vtx in E. pose proof (to_Z_bounded a). pose proof (to_Z_bounded b).
  apply to_Z_inj. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Correctness                                                         *)
(* ------------------------------------------------------------------ *)

Section Glue.

Variables (n0 d0 : N) (st ri rj rk : list N) (x y : uint) (xs xi xj xk : array int).
Hypothesis Hv : valid_input n0 d0 st ri rj rk.
Hypothesis Hx : repr x n0.
Hypothesis Hy : repr y d0.
Hypothesis Hxs : @repr (array uint) (list N) _ xs st.
Hypothesis Hxi : @repr (array uint) (list N) _ xi ri.
Hypothesis Hxj : @repr (array uint) (list N) _ xj rj.
Hypothesis Hxk : @repr (array uint) (list N) _ xk rk.

Lemma Hn : (2 <= (φ x) <= 500)%Z.
Proof. destruct Hv. unfold repr, repr_uint in Hx. lia. Qed.

Lemma Hn0 : Z.of_N n0 = (φ x).
Proof. unfold repr, repr_uint in Hx. pose proof (to_Z_bounded x). lia. Qed.

Lemma Hd0 : Z.of_N d0 = (φ y) /\ (0 < (φ y) < 2147483648)%Z.
Proof. destruct Hv. unfold repr, repr_uint in Hy. pose proof (to_Z_bounded y). lia. Qed.

Lemma Hm : (φ (PArray.length xi)) = Z.of_nat (List.length ri) /\
  Z.of_nat (List.length rj) = Z.of_nat (List.length ri) /\
  Z.of_nat (List.length rk) = Z.of_nat (List.length ri) /\
  (Z.of_nat (List.length ri) <= 250000)%Z.
Proof.
  pose proof Hn as HnZ. pose proof Hn0.
  pose proof (repr_len_u xi ri Hxi) as E.
  destruct Hv. unfold len in *.
  split; [exact E|]. split; [lia|]. split; [lia|].
  assert (n0 * (n0 - 1) <= 500 * 500)%N by nia.
  pose proof (N.Div0.div_le_upper_bound (n0 * (n0 - 1)) 2 (500 * 500) ltac:(lia)).
  lia.
Qed.

Lemma Hedge_ok : forall e : int, ((φ e) < (φ (PArray.length xi)))%Z ->
  (1 <= (φ (xi.[e])) <= (φ x))%Z /\ (1 <= (φ (xj.[e])) <= (φ x))%Z /\
  road ri rj rk (Z.to_N (φ (xi.[e]))) (Z.to_N (φ (xj.[e]))) (Z.to_N (φ (xk.[e]))).
Proof.
  intros e He. destruct Hm as (Hm1 & Hm2 & Hm3 & _). rewrite Hm1 in He.
  pose proof Hn0.
  rewrite (repr_get_u xi ri Hxi e He).
  rewrite (repr_get_u xj rj Hxj e ltac:(lia)).
  rewrite (repr_get_u xk rk Hxk e ltac:(lia)).
  pose proof (Forall2_nth' _ _ _ 0%N 0%N (vi_ij _ _ _ _ _ _ Hv) (Z.to_nat (φ e)) ltac:(lia))
    as Hij.
  unfold Prelude.get. rewrite !Z_N_nat. cbv beta in Hij.
  split; [lia|]. split; [lia|]. rewrite !N2Z.id.
  exists (Z.to_N (φ e)). unfold Prelude.get, len. rewrite !Z_N_nat. split; [lia|].
  split; [reflexivity|]. left. split; reflexivity.
Qed.

Lemma Hroad_ok : forall u v k, road ri rj rk u v k -> exists e, ((φ e) < (φ (PArray.length xi)))%Z /\
  Z.of_N k = (φ (xk.[e])) /\
  ((Z.of_N u = (φ (xi.[e])) /\ Z.of_N v = (φ (xj.[e]))) \/
   (Z.of_N u = (φ (xj.[e])) /\ Z.of_N v = (φ (xi.[e])))).
Proof.
  intros u v k (e & He & Hk & Huv). destruct Hm as (Hm1 & Hm2 & Hm3 & Hm4).
  unfold len in He.
  exists (of_Z (Z.of_N e)).
  assert (Ee : (φ (of_Z (Z.of_N e))) = Z.of_N e).
  { rewrite of_Z_spec. apply Z.mod_small.
    assert (wB = 9223372036854775808%Z) by reflexivity. lia. }
  rewrite Hm1, Ee.
  rewrite (repr_get_u xi ri Hxi _ ltac:(rewrite Ee; lia)).
  rewrite (repr_get_u xj rj Hxj _ ltac:(rewrite Ee; lia)).
  rewrite (repr_get_u xk rk Hxk _ ltac:(rewrite Ee; lia)).
  rewrite Ee, N2Z.id. split; [lia|]. split; [rewrite Hk; reflexivity|].
  destruct Huv as [[-> ->] | [-> ->]]; [left | right]; split; reflexivity.
Qed.

Lemma Hrange_ok : forall u v k, road ri rj rk u v k -> (1 <= Z.of_N v <= (φ x))%Z.
Proof.
  intros u v k (e & He & Hk & Huv). pose proof Hn0. destruct Hm as (_ & Hm2 & _).
  unfold len in He.
  pose proof (Forall2_nth' _ _ _ 0%N 0%N (vi_ij _ _ _ _ _ _ Hv) (N.to_nat e) ltac:(lia))
    as Hij.
  unfold Prelude.get in Huv. cbv beta in Hij.
  destruct Huv as [[_ <-] | [<- _]]; lia.
Qed.

Definition T0 : array int :=
  diag_loop x 0 (PArray.make (x * x) INF) (Zwf_well_founded 0 (gap x 0)).
Definition T1 : array int :=
  edge_loop x xi xj xk (PArray.length xi) 0 T0
    (Zwf_well_founded 0 (gap (PArray.length xi) 0)).
Definition TT : array int := fw_k x 0 T1 (Zwf_well_founded 0 (gap x 0)).

Lemma TT_inv : fwinv x ri rj rk (φ x) TT.
Proof.
  pose proof Hn as HnZ.
  unfold TT. eapply fw_k_spec; [exact HnZ | reflexivity | change (φ 0) with 0%Z; lia |].
  change (φ 0) with 0%Z.
  apply (einv_fwinv x ri rj rk xi xj xk (PArray.length xi) Hedge_ok Hroad_ok).
  unfold T1. eapply edge_spec; [exact HnZ | exact Hedge_ok | reflexivity
    | change (φ 0) with 0%Z; pose proof (to_Z_bounded (PArray.length xi)); lia |].
  split.
  - apply dinv_base. unfold T0. eapply diag_spec; [exact HnZ | reflexivity
      | change (φ 0) with 0%Z; lia |].
    assert (HL : (φ (PArray.length (PArray.make (x * x) INF))) = ((φ x) * (φ x))%Z).
    { rewrite alength_make.
      assert (Hxx : (φ (x * x)) = ((φ x) * (φ x))%Z).
      { rewrite mul_spec. apply Z.mod_small.
        assert (wB = 9223372036854775808%Z) by reflexivity. nia. }
      replace (x * x <=? PArray.max_length) with true; [exact Hxx|].
      symmetry. rewrite leb_spec, Hxx. change (φ PArray.max_length) with 4194303%Z. nia. }
    split; [exact HL|].
    intros a b Ha Hb. unfold C. rewrite aget_make.
    change (φ 0) with 0%Z. pose proof (to_Z_bounded a).
    destruct (Z.ltb_spec (φ a) 0); [lia|]. rewrite Bool.andb_false_r. reflexivity.
  - intros e' He'. pose proof (to_Z_bounded e'). change (φ 0) with 0%Z in He'. lia.
Qed.

Lemma Ht_ok : (φ (PArray.length xs)) = Z.of_nat (List.length st) /\
  (0 < (φ (PArray.length xs)) < (φ x))%Z.
Proof.
  pose proof (repr_len_u xs st Hxs) as E. pose proof Hn0.
  destruct Hv. unfold len in *. split; [exact E | lia].
Qed.

Lemma Hxs_ok : forall i, ((φ i) < (φ (PArray.length xs)))%Z ->
  (φ (xs.[i])) = Z.of_N (Prelude.get st (Z.to_N (φ i))) /\
  (2 <= (φ (xs.[i])) <= (φ x) - 1)%Z.
Proof.
  intros i Hi. destruct Ht_ok as [E _]. rewrite E in Hi. pose proof Hn0.
  rewrite (repr_get_u xs st Hxs i Hi). split; [reflexivity|].
  pose proof (proj1 (Forall_nth _ _) (vi_st _ _ _ _ _ _ Hv) (Z.to_nat (φ i)) 0%N
                ltac:(lia)) as Hs.
  cbv beta in Hs. unfold Prelude.get. rewrite Z_N_nat. lia.
Qed.

Definition tS : int := PArray.length xs.
Definition MM : int := tS + 2.
Definition tg : int := tS + 1.
Definition VV : array int :=
  vx_loop xs tS 0 (PArray.make MM 0).[tS + 1 <- x - 1] (Zwf_well_founded 0 (gap tS 0)).
Definition ww (a b : int) : Z := C x TT (VV.[a]) (VV.[b]).

Lemma MM_val : (φ MM) = ((φ tS) + 2)%Z /\ (φ tg) = ((φ tS) + 1)%Z /\ (0 < (φ tS) < (φ x))%Z.
Proof.
  destruct Ht_ok as [_ Hb]. pose proof Hn. fold tS in Hb.
  unfold MM, tg. split; [|split; [|exact Hb]]; sia.
Qed.

Lemma VV_inv : vxinv x xs tS tS VV.
Proof.
  destruct MM_val as (HM & Htg & Hb). pose proof Hn.
  unfold VV. eapply vx_spec; [lia | | reflexivity | change (φ 0) with 0%Z; lia |].
  - intros i Hi. destruct (Hxs_ok i Hi). lia.
  - assert (HL : (φ (PArray.length (PArray.make MM 0))) = (φ MM)).
    { rewrite alength_make. replace (MM <=? PArray.max_length) with true; [reflexivity|].
      symmetry. rewrite leb_spec. change (φ PArray.max_length) with 4194303%Z. lia. }
    assert (Hlt : (tS + 1 <? PArray.length (PArray.make MM 0)) = true).
    { rewrite ltb_spec, HL. change (tS + 1) with tg. lia. }
    split; [rewrite alength_set, HL; exact HM|].
    split.
    + rewrite aget_set_other, aget_make; [reflexivity|].
      intro F. assert ((φ (tS + 1)) = (φ 0)) by (rewrite F; reflexivity).
      fold tg in *. change (φ 0) with 0%Z in *. lia.
    + split.
      * rewrite aget_set_same by exact Hlt. apply sub1_val. lia.
      * intros a Ha. change (φ 0) with 0%Z in Ha. lia.
Qed.

Lemma node_cases : forall a, ((φ a) < (φ MM))%Z ->
  (a = 0 /\ (φ (VV.[a])) = 0%Z) \/ (a = tg /\ (φ (VV.[a])) = ((φ x) - 1)%Z) \/
  ((1 <= (φ a) <= (φ tS))%Z /\ (φ (VV.[a])) = ((φ (xs.[a - 1])) - 1)%Z).
Proof.
  intros a Ha. destruct MM_val as (HM & Htg & Hb).
  destruct VV_inv as (_ & H0 & H1 & H2).
  destruct (Z.eq_dec (φ a) 0) as [E | E].
  - left. assert (a = 0) by (apply to_Z_inj; exact E). subst. split; [reflexivity | exact H0].
  - destruct (Z.eq_dec (φ a) ((φ tS) + 1)) as [E' | E'].
    + right; left. assert (a = tg) by (apply to_Z_inj; lia). subst.
      split; [reflexivity | exact H1].
    + right; right. split; [lia|]. apply H2. lia.
Qed.

Lemma Vrange : forall a, ((φ a) < (φ MM))%Z -> inr x (VV.[a]).
Proof.
  intros a Ha. pose proof Hn. destruct MM_val as (HM & Htg & Hb). unfold inr.
  destruct (node_cases a Ha) as [(_ & E) | [(_ & E) | (Ha' & E)]]; rewrite E; [lia | lia |].
  assert (Hi : ((φ (a - 1)) < (φ (PArray.length xs)))%Z) by (rewrite sub1_val by lia; change (PArray.length xs) with tS; lia).
  destruct (Hxs_ok _ Hi). lia.
Qed.

Lemma V0 : vtx (VV.[0]) = 1%N.
Proof. destruct VV_inv as (_ & H0 & _). unfold vtx. rewrite H0. reflexivity. Qed.

Lemma Vtg : vtx (VV.[tg]) = n0.
Proof.
  destruct VV_inv as (_ & _ & H1 & _). pose proof Hn0. pose proof Hn.
  unfold vtx, tg. rewrite H1. lia.
Qed.

Lemma refill_node : forall a, ((φ a) < (φ tg))%Z -> refill st (vtx (VV.[a])).
Proof.
  intros a Ha. destruct MM_val as (HM & Htg & Hb).
  destruct (node_cases a ltac:(lia)) as [(-> & _) | [(-> & _) | (Ha' & E)]].
  - rewrite V0. left. reflexivity.
  - lia.
  - right. assert (Hi : ((φ (a - 1)) < (φ (PArray.length xs)))%Z) by (rewrite sub1_val by lia; change (PArray.length xs) with tS; lia).
    destruct (Hxs_ok _ Hi) as [Ex Bx].
    unfold vtx. rewrite E. replace ((φ (xs.[a - 1])) - 1 + 1)%Z with (φ (xs.[a - 1])) by lia.
    rewrite Ex, N2Z.id. unfold Prelude.get. apply nth_In.
    destruct Ht_ok as [EL _]. rewrite sub1_val in * by lia. lia.
Qed.

Lemma node_of_refill : forall v, refill st v ->
  exists c, ((φ c) < (φ tg))%Z /\ vtx (VV.[c]) = v.
Proof.
  intros v [-> | Hin].
  - exists 0. split; [destruct MM_val as (_ & Htg & _); change (φ 0) with 0%Z; lia|].
    exact V0.
  - destruct (In_nth st v 0%N Hin) as (k & Hk & Ek).
    destruct MM_val as (HM & Htg & Hb). destruct Ht_ok as [EL _]. fold tS in EL.
    set (c := of_Z (Z.of_nat k + 1)).
    assert (Ec : (φ c) = (Z.of_nat k + 1)%Z).
    { unfold c. rewrite of_Z_spec. apply Z.mod_small.
      assert (wB = 9223372036854775808%Z) by reflexivity. lia. }
    exists c. split; [lia|].
    destruct (node_cases c ltac:(lia)) as [(E & _) | [(E & _) | (Hc & E)]].
    + subst c. rewrite E in Ec. change (φ 0) with 0%Z in Ec. lia.
    + rewrite E in Ec. lia.
    + assert (Hi : ((φ (c - 1)) < (φ (PArray.length xs)))%Z) by (rewrite sub1_val by lia; change (PArray.length xs) with tS; lia).
      destruct (Hxs_ok _ Hi) as [Ex Bx].
      unfold vtx. rewrite E. replace ((φ (xs.[c - 1])) - 1 + 1)%Z with (φ (xs.[c - 1])) by lia.
      rewrite Ex, N2Z.id. unfold Prelude.get. rewrite sub1_val by lia.
      rewrite Ec. replace (Z.to_N (Z.of_nat k + 1 - 1)) with (N.of_nat k) by lia.
      rewrite Nnat.Nat2N.id. exact Ek.
Qed.

Lemma ww_nonneg : forall a b, (0 <= ww a b)%Z.
Proof. intros. apply C_nonneg. Qed.

Lemma ww_walk : forall a b, ((φ a) < (φ MM))%Z -> ((φ b) < (φ MM))%Z -> (ww a b <= (φ y))%Z ->
  walk ri rj rk (vtx (VV.[a])) (vtx (VV.[b])) (Z.to_N (ww a b)) /\
  (Z.to_N (ww a b) <= d0)%N.
Proof.
  intros a b Ha Hb Hw. destruct Hd0 as [Ed Bd]. split; [|lia].
  exact (fi_walk x ri rj rk (φ x) TT TT_inv (VV.[a]) (VV.[b]) (Vrange a Ha) (Vrange b Hb)
           ltac:(unfold ww in Hw; rewrite INF_val; lia)).
Qed.

Lemma HMM : (2 <= (φ MM) <= 501)%Z.
Proof. destruct MM_val as (HM & _ & Hb). pose proof Hn. lia. Qed.

Lemma sound : forall b L, dp MM tg y ww b L ->
  (b <> tg -> forall L', trip n0 d0 st ri rj rk (vtx (VV.[b])) L' ->
     trip n0 d0 st ri rj rk 1 (Z.to_N L + L')) /\
  (b = tg -> trip n0 d0 st ri rj rk 1 (Z.to_N L)).
Proof.
  intros b L H. destruct MM_val as (HM & Htg & Hb).
  induction H as [| a b L H IH Ha Hb' Hwab].
  - split.
    + intros _ L' HT. rewrite V0 in HT. exact HT.
    + intros E. assert ((φ 0) = (φ tg)) by (rewrite E; reflexivity).
      change (φ 0) with 0%Z in *. lia.
  - destruct IH as [IH1 _].
    destruct (dp_range MM tg y ww HMM ww_nonneg a L H) as [Har HL].
    destruct (ww_walk a b Har Hb' Hwab) as [HW Hle].
    pose proof (ww_nonneg a b).
    split.
    + intros Hbt L' HT.
      assert (Hb2 : ((φ b) < (φ tg))%Z).
      { destruct (Z.eq_dec (φ b) (φ tg)) as [E|E]; [|lia].
        exfalso. apply Hbt. apply to_Z_inj. exact E. }
      pose proof (IH1 Ha (Z.to_N (ww a b) + L')%N
        (trip_refill _ _ _ _ _ _ _ _ _ _ HW Hle (refill_node b Hb2) HT)) as R.
      rewrite Z2N.inj_add by lia. rewrite <- N.add_assoc. exact R.
    + intros ->. rewrite Vtg in HW.
      pose proof (IH1 Ha (Z.to_N (ww a tg)) (trip_home _ _ _ _ _ _ _ _ HW Hle)) as R.
      rewrite Z2N.inj_add by lia. exact R.
Qed.

Lemma complete : forall u L, trip n0 d0 st ri rj rk u L ->
  forall a L0, dp MM tg y ww a L0 -> a <> tg -> u = vtx (VV.[a]) ->
  exists L'', dp MM tg y ww tg L'' /\ (L'' <= L0 + Z.of_N L)%Z.
Proof.
  destruct MM_val as (HM & Htg & Hb). destruct Hd0 as [Ed Bd].
  intros u L HT. induction HT as [u L HW HLd | u v L L' HW HLd Hrf HT IH];
    intros a L0 Hdp Hat Hu.
  - destruct (dp_range MM tg y ww HMM ww_nonneg a L0 Hdp) as [Har HL0].
    destruct (fw_lower x Hn ri rj rk TT TT_inv Hrange_ok u n0 L HW (VV.[a])
                (Vrange a Har) Hu) as (b' & Hb' & Eb' & Cb').
    rewrite <- Vtg in Eb'. apply vtx_inj in Eb'. subst b'.
    exists (L0 + ww a tg)%Z. split.
    + apply dp_step; [exact Hdp | exact Hat | lia |]. unfold ww. lia.
    + unfold ww. lia.
  - destruct (dp_range MM tg y ww HMM ww_nonneg a L0 Hdp) as [Har HL0].
    destruct (fw_lower x Hn ri rj rk TT TT_inv Hrange_ok u v L HW (VV.[a])
                (Vrange a Har) Hu) as (b' & Hb' & Eb' & Cb').
    destruct (node_of_refill v Hrf) as (c & Hc & Ec).
    rewrite <- Ec in Eb'. apply vtx_inj in Eb'. subst b'.
    assert (Hdc : dp MM tg y ww c (L0 + ww a c)).
    { apply dp_step; [exact Hdp | exact Hat | lia |]. unfold ww. lia. }
    assert (Hct : c <> tg) by (intro F; subst c; lia).
    destruct (IH c _ Hdc Hct (eq_sym Ec)) as (L'' & HL'' & Hle).
    exists L''. split; [exact HL''|]. unfold ww in *. lia.
Qed.

Lemma init_dji : dji MM tg y ww (PArray.make MM false) (PArray.make MM INF).[0 <- 0].
Proof.
  destruct MM_val as (HM & Htg & Hb). pose proof Hn.
  assert (Hmax : (MM <=? PArray.max_length) = true).
  { rewrite leb_spec. change (φ PArray.max_length) with 4194303%Z. lia. }
  assert (HL : PArray.length (PArray.make MM INF) = MM) by (rewrite alength_make, Hmax; reflexivity).
  assert (H0 : (0 <? PArray.length (PArray.make MM INF)) = true)
    by (rewrite ltb_spec, HL; change (φ 0) with 0%Z; lia).
  assert (Dget : forall a, (φ ((PArray.make MM INF).[0 <- 0].[a])) =
            if (a =? 0) then 0%Z else (φ INF)).
  { intros a. destruct (eqbP a 0) as [-> | E].
    - rewrite aget_set_same by exact H0. reflexivity.
    - rewrite aget_set_other by (intro F; apply E; symmetry; exact F).
      rewrite aget_make. reflexivity. }
  constructor.
  - rewrite blength_make, Hmax. reflexivity.
  - rewrite alength_set, HL. reflexivity.
  - intros a _. rewrite Dget. destruct (a =? 0); rewrite INF_val; lia.
  - rewrite Dget. reflexivity.
  - intros a _ Hlt. rewrite Dget in *. destruct (eqbP a 0) as [Ea | E]; [subst a | lia].
    apply dp_src.
  - intros a _ Va. rewrite bget_make in Va. discriminate.
  - intros a b _ _ Va. rewrite bget_make in Va. discriminate.
  - apply bget_make.
Qed.

Lemma glue_correct : exists o : option N,
  repr (slowleak_impl x y xs xi xj xk) o /\ slowleak_spec n0 d0 st ri rj rk o.
Proof.
  destruct MM_val as (HM & Htg & Hb). destruct Hd0 as [Ed Bd].
  assert (Eimpl : slowleak_impl x y xs xi xj xk =
    dij_loop x MM tg VV TT y MM (PArray.make MM false) (PArray.make MM INF).[0 <- 0]
      (Zwf_well_founded 0 (φ MM))) by reflexivity.
  pose proof (dij_spec x MM tg y VV TT ww HMM ltac:(lia) ltac:(lia) ww_nonneg
                ltac:(intros; reflexivity) _ MM _ _ (Zwf_well_founded 0 (φ MM)) eq_refl
                init_dji ltac:(rewrite ucnt_make; reflexivity)) as R.
  rewrite Eimpl.
  destruct (dij_loop x MM tg VV TT y MM (PArray.make MM false) (PArray.make MM INF).[0 <- 0]
              (Zwf_well_founded 0 (φ MM))) as [D |]; simpl in R.
  - destruct R as [R1 R2].
    exists (Some (Z.to_N (φ D))). split; [reflexivity|].
    split.
    + exact (proj2 (sound tg (φ D) R1) eq_refl).
    + intros L HT.
      assert (Ht0 : (0 : int) <> tg) by (intro F; rewrite <- F in Htg; change (φ 0) with 0%Z in Htg; lia).
      destruct (complete 1 L HT 0 0 (dp_src MM tg y ww) Ht0 (eq_sym V0)) as (L'' & HL'' & Hle).
      pose proof (R2 L'' HL''). lia.
  - exists None. split; [exact I|].
    intros L HT.
    apply (dn_min (fun L => trip n0 d0 st ri rj rk 1 L) L HT).
    intros (D0 & HD0 & Hmin).
    pose proof (vi_answer _ _ _ _ _ _ Hv D0 (conj HD0 Hmin)) as [_ Hlt].
    assert (Ht0 : (0 : int) <> tg) by (intro F; rewrite <- F in Htg; change (φ 0) with 0%Z in Htg; lia).
    destruct (complete 1 D0 HD0 0 0 (dp_src MM tg y ww) Ht0 (eq_sym V0)) as (L'' & HL'' & Hle).
    pose proof (R L'' HL''). rewrite INF_val in *. lia.
Qed.

End Glue.

Lemma slowleak_impl_correct :
  forall (n d : N) (st ri rj rk : list N)
         (x y : uint) (xs xi xj xk : array uint),
  valid_input n d st ri rj rk ->
  repr x n -> repr y d -> repr xs st ->
  repr xi ri -> repr xj rj -> repr xk rk ->
  exists o : option N,
    repr (slowleak_impl x y xs xi xj xk) o /\ slowleak_spec n d st ri rj rk o.
Proof.
  intros n d st ri rj rk x y xs xi xj xk Hv Hx Hy Hxs Hxi Hxj Hxk.
  exact (glue_correct n d st ri rj rk x y xs xi xj xk Hv Hx Hy Hxs Hxi Hxj Hxk).
Qed.

Definition slowleak_correct :
  forall (n d : N) (st ri rj rk : list N)
         (x y : uint) (xs xi xj xk : array uint),
  valid_input n d st ri rj rk ->
  repr x n -> repr y d -> repr xs st ->
  repr xi ri -> repr xj rj -> repr xk rk ->
  exists o : option N,
    repr (slowleak x y xs xi xj xk) o /\ slowleak_spec n d st ri rj rk o
  := slowleak_impl_correct.
