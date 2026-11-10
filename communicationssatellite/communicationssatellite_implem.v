(* Implementation of communicationssatellite.spec : the minimum total beam
   length, as the weight of a minimum spanning tree.

   Code (Part 5).  Dense Prim, O(n^2) : the complete graph on the dishes,
   edge i j weighing  sqrt (dx^2 + dy^2) - (r_i + r_j)  in binary64 (the
   squared distance and r_i + r_j are exact in int, then converted).  One
   flat [array bool] (in tree), one flat [array float] (best known weight
   to the tree), threaded linearly; each round scans for the minimum key
   ([amin_step]), adds it to the float total, then updates the keys from
   the new dish ([upd_step]).  Every loop is the combinator [loop],
   terminating by an erased Acc on hi - i ; no nat, no Z, no list in the code.

   Proof.
   - Part 1 : Prim on an abstract symmetric weight W >= 0 ([run] : the
     sequence of greedy steps).  [prim_lower] : the cost of any run is at
     most the cost of any edge list connecting every vertex to the start
     (exchange argument on the first edge leaving the tree);
     [run_exists] : a run exists for any weight.
   - Parts 2-3 : plane geometry ([dist_tri], its equality case [tri_eq]);
     the exact weight w i j = |c_i c_j| - r_i - r_j ; the segment of the
     centre line between two dishes ([seg_pts]).  [occl] : the beam of a
     Prim step enters no dish ; [apart_core] : beams of two Prim steps share
     no point (a common point forces a collinear configuration in which a
     centre lies on a beam).
   - Part 4 : the exact run's tree, beams along the centre lines of its
     positive-weight edges ([design]), is compliant and costs the run's
     weight ; every compliant design yields a connecting edge list (touching
     pairs, and for each beam the dishes it meets sorted along it) of
     weight at most its length ([lower_bound]).  Hence [exact_min] : the
     exact Prim weight m is the minimum cost.
   - Part 6 : the program performs a Prim run on the float weights Wh
     (comparisons are exact on floats) ; |Wh - w| <= 4000 u per edge, so the
     Wh-optimum is within 2000 * 4000 u of m (prim_lower both ways), and the
     float sum of the n - 1 chosen keys has relative error <= 2000 u
     ([acc_err]) : the output is within 10^-6 of m, absolutely when m <= 1,
     relatively otherwise.  Nothing is computed exactly in reals at run
     time; the only exact values are the int squared distance and radius sum. *)

From Communicationssatellite.spec Require Import Prelude.
From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals Lra Lia ZifyUint63 Zwf.
From Stdlib Require Import FinFun.
From Stdlib Require Sint63.
From Stdlib Require Import Relation_Operators Operators_Properties Sorting.Sorted Sorting.Permutation Classical_Prop.
From StdGalilei Require Import repr repr_float.
Import ListNotations.

(* ================================================================== *)
(* Part 1. Prim's algorithm on an abstract weighted complete graph     *)
(* ================================================================== *)

Open Scope R_scope.

Section Graph.
Variable W : N -> N -> R.
Variable n : N.

Definition edge (E : list (N * N)) (a b : N) : Prop := In (a, b) E \/ In (b, a) E.

Definition costE (E : list (N * N)) : R :=
  fold_right (fun e s => W (fst e) (snd e) + s) 0 E.

Definition okedge (e : N * N) : Prop := (fst e < n)%N /\ (snd e < n)%N /\ fst e <> snd e.

Definition minp (S : list N) (p v : N) : Prop :=
  forall s t, In s S -> (t < n)%N -> ~ In t S -> W p v <= W s t.

Inductive run : list N -> list (N * N) -> list N -> Prop :=
| run_nil : forall S, run S [] S
| run_cons : forall S p v steps S', In p S -> (v < n)%N -> ~ In v S -> minp S p v ->
    run (v :: S) steps S' -> run S ((p, v) :: steps) S'.

Lemma costE_app : forall E1 E2, costE (E1 ++ E2) = costE E1 + costE E2.
Proof. intros E1 E2; induction E1 as [| e E1 IH]; simpl; [ring | rewrite IH; ring]. Qed.

Hypothesis Wsym : forall i j, W i j = W j i.
Hypothesis Wnn : forall i j, (i < n)%N -> (j < n)%N -> i <> j -> 0 <= W i j.

Lemma costE_nonneg : forall E, Forall okedge E -> 0 <= costE E.
Proof.
  intros E H; induction H as [| e E He _ IH]; simpl; [lra |].
  destruct He as (H1 & H2 & H3). pose proof (Wnn _ _ H1 H2 H3). lra.
Qed.

Lemma crt_mono : forall (R1 R2 : N -> N -> Prop), (forall a b, R1 a b -> R2 a b) ->
  forall a b, clos_refl_trans N R1 a b -> clos_refl_trans N R2 a b.
Proof.
  intros R1 R2 H a b C; induction C; [apply rt_step; auto | apply rt_refl | eapply rt_trans; eauto].
Qed.

Lemma crt_sym : forall (R1 : N -> N -> Prop), (forall a b, R1 a b -> R1 b a) ->
  forall a b, clos_refl_trans N R1 a b -> clos_refl_trans N R1 b a.
Proof.
  intros R1 H a b C; induction C; [apply rt_step; auto | apply rt_refl | eapply rt_trans; eauto].
Qed.

Lemma edge_sym : forall E a b, edge E a b -> edge E b a.
Proof. unfold edge; tauto. Qed.

Lemma crt_edge_sym : forall E a b, clos_refl_trans N (edge E) a b -> clos_refl_trans N (edge E) b a.
Proof. intros E; apply crt_sym, edge_sym. Qed.

Lemma exit_edge : forall E S v s, clos_refl_trans_1n N (edge E) v s -> In s S -> ~ In v S ->
  exists a b, edge E a b /\ ~ In a S /\ In b S /\
    clos_refl_trans_1n N (fun x y => edge E x y /\ ~ In x S /\ ~ In y S) v a.
Proof.
  intros E S v s C; induction C as [v | v y s Hvy C IH]; intros Hs Hv.
  - contradiction.
  - destruct (in_dec N.eq_dec y S) as [Hy | Hy].
    + exists v, y. repeat split; auto. apply rt1n_refl.
    + destruct (IH Hs Hy) as (a & b & Hab & Ha & Hb & P).
      exists a, b. repeat split; auto. econstructor; [| exact P]. auto.
Qed.

Lemma edge_split : forall E a b, edge E a b ->
  exists E1 E2 e, E = E1 ++ e :: E2 /\ (e = (a, b) \/ e = (b, a)).
Proof.
  intros E a b [H | H]; apply in_split in H as (E1 & E2 & ->); exists E1, E2; eauto.
Qed.

Lemma edge_remove : forall E1 E2 e x y, edge (E1 ++ e :: E2) x y ->
  edge (E1 ++ E2) x y \/ e = (x, y) \/ e = (y, x).
Proof.
  intros E1 E2 e x y [H | H]; apply in_app_or in H as [H | [H | H]];
    unfold edge; auto using in_or_app.
Qed.

Lemma edge_keep : forall E1 E2 e x y, edge (E1 ++ E2) x y -> edge (E1 ++ e :: E2) x y.
Proof.
  intros E1 E2 e x y [H | H]; apply in_app_or in H as [H | H]; unfold edge;
    [left | left | right | right]; apply in_or_app; simpl; auto.
Qed.

Lemma prim_lower : forall S steps S', run S steps S' -> forall E, Forall okedge E ->
  (forall x, (x < n)%N -> exists s, In s S /\ clos_refl_trans N (edge E) x s) ->
  costE steps <= costE E.
Proof.
  intros S steps S' R; induction R as [S | S p v steps S' Hp Hv HvS Hmin R IH];
    intros E Eok Conn.
  - simpl. apply costE_nonneg, Eok.
  - destruct (Conn v Hv) as (s & Hs & Cv).
    apply clos_rt_rt1n in Cv.
    destruct (exit_edge E S v s Cv Hs HvS) as (a & b & Hab & Ha & Hb & P).
    destruct (edge_split E a b Hab) as (E1 & E2 & e & -> & He).
    set (E' := E1 ++ E2).
    assert (Hcost : costE (E1 ++ e :: E2) = W (fst e) (snd e) + costE E').
    { unfold E'. rewrite !costE_app. simpl. ring. }
    assert (Eok' : Forall okedge E').
    { unfold E'. rewrite Forall_app in Eok |- *. destruct Eok as [O1 O2].
      inversion O2; subst. auto. }
    assert (Heok : okedge e).
    { rewrite Forall_forall in Eok. apply Eok. apply in_or_app. simpl. auto. }
    assert (Wle : W p v <= W (fst e) (snd e)).
    { destruct He as [-> | ->]; simpl in *; destruct Heok as (H1 & H2 & _).
      - rewrite (Wsym a b). apply Hmin; auto.
      - apply Hmin; auto. }
    (* the non-S path from v to a survives *)
    assert (Pa : clos_refl_trans N (edge E') v a).
    { assert (PP : forall x y, clos_refl_trans_1n N
          (fun x y => edge (E1 ++ e :: E2) x y /\ ~ In x S /\ ~ In y S) x y ->
          clos_refl_trans N (edge E') x y).
      { intros x y P'. induction P' as [x | x y z [Hxy [Hx Hy]] P' IHP].
        - apply rt_refl.
        - eapply rt_trans; [| exact IHP]. apply rt_step.
          destruct (edge_remove E1 E2 e x y Hxy) as [H | [H | H]]; [exact H | |];
            destruct He as [-> | ->]; inversion H; subst; contradiction. }
      apply PP, P. }
    assert (G : forall x, (x < n)%N -> exists s, In s (v :: S) /\ clos_refl_trans N (edge E') x s).
    { intros x Hx. destruct (Conn x Hx) as (s' & Hs' & Cx).
      apply clos_rt_rt1n in Cx. clear Hx.
      induction Cx as [x | x y z Hxy Cy IHy].
      - exists x. split; [right; exact Hs' | apply rt_refl].
      - destruct (IHy Hs') as (t & Ht & Ct).
        destruct (edge_remove E1 E2 e x y Hxy) as [H | [H | H]].
        + exists t. split; [exact Ht |]. eapply rt_trans; [apply rt_step, H | exact Ct].
        + destruct He as [-> | ->]; inversion H; subst.
          * exists v. split; [left; reflexivity | apply crt_edge_sym, Pa].
          * exists x. split; [right; exact Hb | apply rt_refl].
        + destruct He as [-> | ->]; inversion H; subst.
          * exists x. split; [right; exact Hb | apply rt_refl].
          * exists v. split; [left; reflexivity | apply crt_edge_sym, Pa]. }
    simpl. specialize (IH E' Eok' G). rewrite Hcost. lra.
Qed.

End Graph.

Definition verts (n : N) : list N := map N.of_nat (seq 0 (N.to_nat n)).

Lemma verts_In : forall n x, In x (verts n) <-> (x < n)%N.
Proof.
  intros n x. unfold verts. rewrite in_map_iff. split.
  - intros (k & <- & Hk). apply in_seq in Hk. lia.
  - intros H. exists (N.to_nat x). split; [lia | apply in_seq; lia].
Qed.

Lemma verts_NoDup : forall n, NoDup (verts n).
Proof.
  intros n. unfold verts. apply Injective_map_NoDup; [intros a b H; lia | apply seq_NoDup].
Qed.

Lemma verts_length : forall n, List.length (verts n) = N.to_nat n.
Proof. intros n. unfold verts. rewrite length_map, length_seq. reflexivity. Qed.

Section Runs.
Variable W : N -> N -> R.
Variable n : N.

Lemma run_conn : forall S steps S', run W n S steps S' ->
  forall x, In x S' -> exists s, In s S /\ clos_refl_trans N (edge steps) x s.
Proof.
  intros S steps S' R; induction R as [S | S p v steps S' Hp Hv HvS Hmin R IH]; intros x Hx.
  - exists x. split; [exact Hx | apply rt_refl].
  - destruct (IH x Hx) as (s & [<- | Hs] & C).
    + exists p. split; [exact Hp |]. eapply rt_trans.
      * eapply crt_mono; [| exact C]. intros a b [H | H]; [left | right]; right; exact H.
      * apply rt_step. right. left. reflexivity.
    + exists s. split; [exact Hs |].
      eapply crt_mono; [| exact C]. intros a b [H | H]; [left | right]; right; exact H.
Qed.

Lemma run_ok : forall S steps S', run W n S steps S' -> (forall s, In s S -> (s < n)%N) ->
  Forall (okedge n) steps /\ (forall s, In s S' -> (s < n)%N).
Proof.
  intros S steps S' R; induction R as [S | S p v steps S' Hp Hv HvS Hmin R IH]; intros HS.
  - split; auto.
  - destruct IH as [IH1 IH2]. { intros s [<- | H]; auto. }
    split; [| exact IH2]. constructor; [| exact IH1].
    repeat split; simpl; auto. intros ->. contradiction.
Qed.

Lemma run_nodup : forall S steps S', run W n S steps S' -> NoDup S ->
  NoDup S' /\ List.length S' = (List.length S + List.length steps)%nat.
Proof.
  intros S steps S' R; induction R as [S | S p v steps S' Hp Hv HvS Hmin R IH]; intros HS.
  - simpl. split; auto.
  - destruct IH as [IH1 IH2]; [constructor; auto |].
    split; [exact IH1 |]. rewrite IH2. simpl. lia.
Qed.

Lemma run_incl : forall S steps S', run W n S steps S' -> incl S S'.
Proof.
  intros S steps S' R; induction R; [apply incl_refl |].
  intros x Hx. apply IHR. right. exact Hx.
Qed.

Lemma run_snoc : forall S steps S' p v, run W n S steps S' ->
  In p S' -> (v < n)%N -> ~ In v S' -> minp W n S' p v ->
  run W n S (steps ++ [(p, v)]) (v :: S').
Proof.
  intros S steps S' p v R; induction R; intros; simpl.
  - constructor; auto. constructor.
  - constructor; auto.
Qed.

(* every later step of a run is a step at some larger set *)
Lemma run_later : forall S steps S', run W n S steps S' ->
  forall c d, In (c, d) steps -> exists T, incl S T /\ In c T /\ ~ In d T /\ (d < n)%N /\
    minp W n T c d.
Proof.
  intros S steps S' R; induction R as [S | S p v steps S' Hp Hv HvS Hmin R IH];
    intros c d Hin; [destruct Hin |].
  destruct Hin as [E | Hin].
  - inversion E; subst. exists S. repeat split; auto. apply incl_refl.
  - destruct (IH c d Hin) as (T & HT & H1 & H2 & H3 & H4).
    exists T. repeat split; auto. intros x Hx. apply HT. right. exact Hx.
Qed.

Lemma exists_min : forall {A} (f : A -> R) (l : list A), l <> [] ->
  exists x, In x l /\ forall y, In y l -> f x <= f y.
Proof.
  intros A f l; induction l as [| a l IH]; intros Hl; [congruence |].
  destruct l as [| b l].
  - exists a. split; [left; auto |]. intros y [<- | []]. lra.
  - destruct (IH ltac:(discriminate)) as (x & Hx & Hm).
    destruct (Rle_or_lt (f a) (f x)) as [H | H].
    + exists a. split; [left; auto |]. intros y [<- | Hy]; [lra |]. specialize (Hm y Hy). lra.
    + exists x. split; [right; auto |]. intros y [<- | Hy]; [lra | auto].
Qed.

Lemma run_exists : forall S, (forall s, In s S -> (s < n)%N) -> S <> [] -> NoDup S ->
  exists steps S', run W n S steps S' /\ forall x, (x < n)%N -> In x S'.
Proof.
  intros S. remember (N.to_nat n - List.length S)%nat as k eqn:Ek. revert S Ek.
  induction k as [k IH] using (well_founded_induction lt_wf).
  intros S Ek HS Hne Hnd.
  set (C := filter (fun t => if in_dec N.eq_dec t S then false else true) (verts n)).
  destruct C as [| v0 C0] eqn:EC.
  - exists [], S. split; [constructor |]. intros x Hx.
    destruct (in_dec N.eq_dec x S) as [H | H]; [exact H | exfalso].
    assert (In x C) by (unfold C; apply filter_In; split; [apply verts_In; auto |];
      destruct (in_dec N.eq_dec x S); [contradiction | reflexivity]).
    rewrite EC in H0. destruct H0.
  - assert (HC : C <> []) by (rewrite EC; discriminate).
    assert (HP : list_prod S C <> []).
    { destruct S as [| s S0]; [congruence |]. rewrite EC. simpl. discriminate. }
    destruct (exists_min (fun e => W (fst e) (snd e)) _ HP) as ([p v] & Hin & Hm).
    apply in_prod_iff in Hin as [Hp Hv].
    unfold C in Hv. apply filter_In in Hv as [Hv Hv'].
    destruct (in_dec N.eq_dec v S) as [_ | HvS]; [discriminate |].
    apply verts_In in Hv.
    assert (Hmin : minp W n S p v).
    { intros s t Hs Ht HtS. apply (Hm (s, t)). apply in_prod; [exact Hs |].
      unfold C. apply filter_In. split; [apply verts_In; exact Ht |].
      destruct (in_dec N.eq_dec t S); [contradiction | reflexivity]. }
    assert (Hlen : (List.length (v :: S) <= N.to_nat n)%nat).
    { rewrite <- (verts_length n). apply NoDup_incl_length; [constructor; auto |].
      intros x [<- | Hx]; apply verts_In; auto. }
    destruct (IH (N.to_nat n - List.length (v :: S))%nat ltac:(simpl in *; lia) (v :: S) eq_refl)
      as (steps & S' & R & All).
    + intros x [<- | Hx]; auto.
    + discriminate.
    + constructor; auto.
    + exists ((p, v) :: steps), S'. split; [constructor; auto | exact All].
Qed.

End Runs.

Lemma costE_diff : forall (W1 W2 : N -> N -> R) (dl : R) E,
  (forall e, In e E -> Rabs (W1 (fst e) (snd e) - W2 (fst e) (snd e)) <= dl) ->
  Rabs (costE W1 E - costE W2 E) <= INR (List.length E) * dl.
Proof.
  intros W1 W2 dl E; induction E as [| e E IH]; intros H.
  - simpl. rewrite Rminus_0_r, Rabs_R0. lra.
  - change (List.length (e :: E)) with (S (List.length E)). rewrite S_INR.
    change (costE W1 (e :: E)) with (W1 (fst e) (snd e) + costE W1 E).
    change (costE W2 (e :: E)) with (W2 (fst e) (snd e) + costE W2 E).
    replace (W1 (fst e) (snd e) + costE W1 E - (W2 (fst e) (snd e) + costE W2 E))
      with ((W1 (fst e) (snd e) - W2 (fst e) (snd e)) + (costE W1 E - costE W2 E)) by ring.
    eapply Rle_trans; [apply Rabs_triang |].
    pose proof (H e (or_introl eq_refl)). pose proof (IH (fun e' He' => H e' (or_intror He'))).
    lra.
Qed.

(* ================================================================== *)
(* Part 2. Plane geometry                                              *)
(* ================================================================== *)

Definition dist (p q : point) : R := sqrt (sqdist p q).

Definition pt (p q : point) (s : R) : point :=
  (fst p + s * (fst q - fst p), snd p + s * (snd q - snd p)).

Lemma sqdist_eq : forall p q, sqdist p q =
  (fst p - fst q) * (fst p - fst q) + (snd p - snd q) * (snd p - snd q).
Proof. intros. unfold sqdist. ring. Qed.

Lemma sum_sq_nonneg : forall a b, 0 <= a * a + b * b.
Proof. intros a b. pose proof (Rle_0_sqr a). pose proof (Rle_0_sqr b). unfold Rsqr in *. lra. Qed.

Lemma sqdist_nonneg : forall p q, 0 <= sqdist p q.
Proof.
  intros p q. rewrite sqdist_eq.
  pose proof (Rle_0_sqr (fst p - fst q)). pose proof (Rle_0_sqr (snd p - snd q)).
  unfold Rsqr in *. lra.
Qed.

Lemma sqdist_sym : forall p q, sqdist p q = sqdist q p.
Proof. intros p q. unfold sqdist. ring. Qed.

Lemma dist_nonneg : forall p q, 0 <= dist p q.
Proof. intros. apply sqrt_pos. Qed.

Lemma dist_sym : forall p q, dist p q = dist q p.
Proof. intros. unfold dist. rewrite sqdist_sym. reflexivity. Qed.

Lemma dist_sq : forall p q, dist p q * dist p q = sqdist p q.
Proof. intros. apply sqrt_sqrt, sqdist_nonneg. Qed.

Lemma sqrt_le_bound : forall X Y, 0 <= Y -> X <= Y * Y -> sqrt X <= Y.
Proof. intros X Y HY H. rewrite <- (sqrt_square Y HY). apply sqrt_le_1_alt. exact H. Qed.

Lemma pt0 : forall p q, pt p q 0 = p.
Proof. intros [a b] q. unfold pt. simpl. f_equal; ring. Qed.

Lemma pt1 : forall p q, pt p q 1 = q.
Proof. intros [a b] [c d]. unfold pt. simpl. f_equal; ring. Qed.

Lemma dist_pt_pt : forall p q s s', dist (pt p q s) (pt p q s') = Rabs (s - s') * dist p q.
Proof.
  intros p q s s'. unfold dist.
  replace (sqdist (pt p q s) (pt p q s')) with (((s - s') * (s - s')) * sqdist p q)
    by (unfold sqdist, pt; simpl; ring).
  rewrite sqrt_mult_alt; [| apply Rle_0_sqr]. change ((s - s') * (s - s')) with (Rsqr (s - s')).
  rewrite sqrt_Rsqr_abs. reflexivity.
Qed.

Lemma dist_tri : forall p z q, dist p q <= dist p z + dist z q.
Proof.
  intros [p1 p2] [z1 z2] [q1 q2]. unfold dist. rewrite !sqdist_eq. cbn [fst snd].
  set (a1 := z1 - p1). set (a2 := z2 - p2). set (b1 := q1 - z1). set (b2 := q2 - z2).
  set (A := sqrt ((p1 - z1) * (p1 - z1) + (p2 - z2) * (p2 - z2))).
  set (B := sqrt ((z1 - q1) * (z1 - q1) + (z2 - q2) * (z2 - q2))).
  assert (HA : A * A = a1 * a1 + a2 * a2) by (unfold A; rewrite sqrt_sqrt by apply sum_sq_nonneg; unfold a1, a2; ring).
  assert (HB : B * B = b1 * b1 + b2 * b2) by (unfold B; rewrite sqrt_sqrt by apply sum_sq_nonneg; unfold b1, b2; ring).
  assert (A0 : 0 <= A) by apply sqrt_pos. assert (B0 : 0 <= B) by apply sqrt_pos.
  apply sqrt_le_bound; [lra |].
  assert (Hab : a1 * b1 + a2 * b2 <= A * B).
  { destruct (Rle_or_lt (a1 * b1 + a2 * b2) 0) as [H | H]; [nra |].
    assert (L : (a1 * b1 + a2 * b2) * (a1 * b1 + a2 * b2) <= (A * B) * (A * B)).
    { replace ((A * B) * (A * B)) with ((A * A) * (B * B)) by ring. rewrite HA, HB.
      pose proof (Rle_0_sqr (a1 * b2 - a2 * b1)). unfold Rsqr in *. nra. }
    apply Rsqr_incr_0_var; [unfold Rsqr; exact L | apply Rmult_le_pos; assumption]. }
  replace ((p1 - q1) * (p1 - q1) + (p2 - q2) * (p2 - q2)) with ((a1 + b1) * (a1 + b1) + (a2 + b2) * (a2 + b2))
    by (unfold a1, a2, b1, b2; ring).
  nra.
Qed.

Lemma tri_eq : forall p z q, dist p q = dist p z + dist z q -> 0 < dist p z ->
  q = pt p z (dist p q / dist p z).
Proof.
  intros [p1 p2] [z1 z2] [q1 q2]. unfold dist, pt. rewrite !sqdist_eq. cbn [fst snd].
  set (A := sqrt ((p1 - z1) * (p1 - z1) + (p2 - z2) * (p2 - z2))).
  set (B := sqrt ((z1 - q1) * (z1 - q1) + (z2 - q2) * (z2 - q2))).
  set (Dq := sqrt ((p1 - q1) * (p1 - q1) + (p2 - q2) * (p2 - q2))).
  intros E HA0.
  assert (HA : A * A = (z1 - p1) * (z1 - p1) + (z2 - p2) * (z2 - p2)) by (unfold A; rewrite sqrt_sqrt by apply sum_sq_nonneg; ring).
  assert (HB : B * B = (q1 - z1) * (q1 - z1) + (q2 - z2) * (q2 - z2)) by (unfold B; rewrite sqrt_sqrt by apply sum_sq_nonneg; ring).
  assert (HD : Dq * Dq = (q1 - p1) * (q1 - p1) + (q2 - p2) * (q2 - p2)) by (unfold Dq; rewrite sqrt_sqrt by apply sum_sq_nonneg; ring).
  assert (B0 : 0 <= B) by apply sqrt_pos.
  set (a1 := z1 - p1) in *. set (a2 := z2 - p2) in *. set (b1 := q1 - z1) in *. set (b2 := q2 - z2) in *.
  assert (Hq1 : q1 - p1 = a1 + b1) by (unfold a1, b1; ring).
  assert (Hq2 : q2 - p2 = a2 + b2) by (unfold a2, b2; ring).
  rewrite Hq1, Hq2 in HD.
  assert (Dot : a1 * b1 + a2 * b2 = A * B).
  { rewrite E in HD. nra. }
  assert (Z0 : (B * a1 - A * b1) * (B * a1 - A * b1) + (B * a2 - A * b2) * (B * a2 - A * b2) = 0).
  { replace ((B * a1 - A * b1) * (B * a1 - A * b1) + (B * a2 - A * b2) * (B * a2 - A * b2))
      with ((B * B) * (a1 * a1 + a2 * a2) - 2 * (A * B) * (a1 * b1 + a2 * b2) + (A * A) * (b1 * b1 + b2 * b2))
      by ring.
    rewrite Dot, <- HA, <- HB. ring. }
  destruct (Rplus_sqr_eq_0 _ _ Z0) as [Z1 Z2].
  assert (Ez1 : z1 = p1 + a1) by (unfold a1; ring).
  assert (Ez2 : z2 = p2 + a2) by (unfold a2; ring).
  assert (Eq1 : q1 = z1 + b1) by (unfold b1; ring).
  assert (Eq2 : q2 = z2 + b2) by (unfold b2; ring).
  rewrite E. clearbody A B Dq a1 a2 b1 b2. rewrite Eq1, Eq2, Ez1, Ez2. f_equal.
  - apply (Rmult_eq_reg_l A); [| lra].
    replace (A * (p1 + (A + B) / A * a1)) with (A * p1 + (A + B) * a1) by (field; lra).
    lra.
  - apply (Rmult_eq_reg_l A); [| lra].
    replace (A * (p2 + (A + B) / A * a2)) with (A * p2 + (A + B) * a2) by (field; lra).
    lra.
Qed.

(* ================================================================== *)
(* Part 3. Dishes: the weights, segments of centre lines, and the     *)
(* geometry of Prim's tree                                             *)
(* ================================================================== *)

Section Dish.
Variables (xs ys : list Z) (rs : list N).
Hypothesis Hv : valid_input xs ys rs.

Local Notation n := (len xs).
Local Notation c := (centre xs ys).
Local Notation r := (radius rs).

Definition w (i j : N) : R := dist (c i) (c j) - r i - r j.
Definition ex (i : N) (z : point) : R := dist (c i) z - r i.

Lemma r_bounds : forall i, (i < n)%N -> 1 <= r i <= 100.
Proof.
  intros i Hi. unfold radius. pose proof (vi_rs _ _ _ Hv) as H. rewrite Forall_forall in H.
  assert (Hin : In (nth (N.to_nat i) rs 0%N) rs).
  { apply nth_In. pose proof (vi_len_rs _ _ _ Hv) as E. unfold len in *. lia. }
  specialize (H _ Hin). split.
  - replace 1 with (IZR (Z.of_N 1)) by reflexivity. apply IZR_le. lia.
  - replace 100 with (IZR (Z.of_N 100)) by reflexivity. apply IZR_le. lia.
Qed.

Lemma nov : forall i j, (i < n)%N -> (j < n)%N -> i <> j -> r i + r j <= dist (c i) (c j).
Proof.
  intros i j Hi Hj Hij. pose proof (vi_no_overlap _ _ _ Hv i j Hi Hj Hij) as H.
  pose proof (r_bounds i Hi). pose proof (r_bounds j Hj).
  unfold dist. rewrite <- (sqrt_square (r i + r j)) by lra. apply sqrt_le_1_alt.
  replace ((r i + r j) * (r i + r j)) with ((r i + r j) ^ 2) by ring. exact H.
Qed.

Lemma w_nonneg : forall i j, (i < n)%N -> (j < n)%N -> i <> j -> 0 <= w i j.
Proof. intros i j Hi Hj Hij. pose proof (nov i j Hi Hj Hij). unfold w. lra. Qed.

Lemma w_sym : forall i j, w i j = w j i.
Proof. intros i j. unfold w. rewrite dist_sym. ring. Qed.

Lemma w_def : forall i j, w i j = dist (c i) (c j) - r i - r j.
Proof. reflexivity. Qed.

Lemma ex_tri : forall i j z, w i j <= ex i z + ex j z.
Proof.
  intros i j z. unfold w, ex. pose proof (dist_tri (c i) z (c j)).
  rewrite (dist_sym z (c j)) in H. lra.
Qed.

(* z lies on the centre line of i and j, outside both dishes *)
Definition seg_pts (i j : N) (z : point) : Prop :=
  exists s, z = pt (c i) (c j) s /\ r i <= s * dist (c i) (c j) /\
    s * dist (c i) (c j) <= dist (c i) (c j) - r j.

Lemma seg_facts : forall i j z, (i < n)%N -> (j < n)%N -> seg_pts i j z ->
  0 <= ex i z /\ 0 <= ex j z /\ w i j = ex i z + ex j z /\ 0 < dist (c i) z /\
  exists l, 0 <= l /\ c j = pt (c i) z l.
Proof.
  intros i j z Hi Hj (s & -> & H1 & H2).
  pose proof (r_bounds i Hi). pose proof (r_bounds j Hj).
  set (D := dist (c i) (c j)) in *.
  assert (D0 : 0 <= D) by apply dist_nonneg.
  assert (Ds : 0 < s * D) by lra.
  assert (s0 : 0 < s).
  { destruct (Rle_or_lt s 0) as [Hs | Hs]; [| exact Hs]. nra. }
  assert (s1 : s * D < D) by lra.
  assert (Di : dist (c i) (pt (c i) (c j) s) = s * D).
  { rewrite <- (pt0 (c i) (c j)) at 1. rewrite dist_pt_pt. rewrite Rminus_0_l, Rabs_Ropp.
    rewrite Rabs_right by lra. reflexivity. }
  assert (Dj : dist (c j) (pt (c i) (c j) s) = D - s * D).
  { rewrite <- (pt1 (c i) (c j)) at 1. rewrite dist_pt_pt.
    rewrite Rabs_right by nra. fold D. ring. }
  unfold ex. rewrite Di, Dj. repeat split; try lra.
  - unfold w. fold D. ring.
  - exists (/ s). split; [left; apply Rinv_0_lt_compat; lra |].
    destruct (c i) as [a b] eqn:Ci. destruct (c j) as [a' b'] eqn:Cj.
    unfold pt; cbn [fst snd]. f_equal; field; lra.
Qed.

Lemma seg_sym : forall i j z, seg_pts i j z -> seg_pts j i z.
Proof.
  intros i j z (s & -> & H1 & H2). exists (1 - s). rewrite (dist_sym (c j) (c i)).
  split; [| split; lra].
  destruct (c i) as [a b]. destruct (c j) as [a' b']. unfold pt; cbn [fst snd]. f_equal; ring.
Qed.

Lemma in_int_dist : forall k z, (k < n)%N -> in_interior xs ys rs k z -> dist (c k) z < r k.
Proof.
  intros k z Hk H. unfold in_interior in H. pose proof (r_bounds k Hk).
  unfold dist. rewrite sqdist_sym. rewrite <- (sqrt_square (r k)) by lra.
  apply sqrt_lt_1_alt. split; [apply sqdist_nonneg |].
  replace (r k * r k) with (r k ^ 2) by ring. exact H.
Qed.

Lemma ray : forall o q t z lq lt, (o < n)%N -> (q < n)%N -> (t < n)%N -> o <> q -> q <> t ->
  0 < dist (c o) z -> c q = pt (c o) z lq -> c t = pt (c o) z lt -> 0 <= lq <= lt ->
  seg_pts o t (c q).
Proof.
  intros o q t z lq lt Ho Hq Ht Hoq Hqt Hrho Eq Et Hl.
  set (rho := dist (c o) z) in *.
  pose proof (nov o q Ho Hq Hoq) as N1. pose proof (nov q t Hq Ht Hqt) as N2.
  pose proof (r_bounds o Ho). pose proof (r_bounds q Hq). pose proof (r_bounds t Ht).
  assert (Doq : dist (c o) (c q) = lq * rho).
  { rewrite Eq. rewrite <- (pt0 (c o) z) at 1. rewrite dist_pt_pt, Rminus_0_l, Rabs_Ropp.
    rewrite Rabs_right by lra. reflexivity. }
  assert (Dqt : dist (c q) (c t) = (lt - lq) * rho).
  { rewrite Eq, Et. rewrite dist_pt_pt. rewrite Rabs_left1 by lra. fold rho. ring. }
  assert (Dot : dist (c o) (c t) = lt * rho).
  { rewrite Et. rewrite <- (pt0 (c o) z) at 1. rewrite dist_pt_pt, Rminus_0_l, Rabs_Ropp.
    rewrite Rabs_right by lra. reflexivity. }
  assert (lq0 : 0 < lq).
  { destruct (Rle_or_lt lq 0) as [Hs | Hs]; [| exact Hs]. assert (lq = 0) by lra. subst lq. lra. }
  assert (lt0 : 0 < lt) by lra.
  exists (lq / lt). rewrite Dot. split; [| split].
  - rewrite Eq, Et. destruct (c o) as [a b]. destruct z as [a' b'].
    unfold pt; cbn [fst snd]. f_equal; field; lra.
  - replace (lq / lt * (lt * rho)) with (lq * rho) by (field; lra). lra.
  - replace (lq / lt * (lt * rho)) with (lq * rho) by (field; lra). lra.
Qed.

(* the beam of a Prim step enters no dish *)
Lemma occl : forall S p v, In p S -> (v < n)%N -> ~ In v S -> (p < n)%N -> minp w n S p v ->
  forall k z, (k < n)%N -> seg_pts p v z -> in_interior xs ys rs k z -> False.
Proof.
  intros S p v Hp Hvn HvS Hpn Hmin k z Hk Hz Hint.
  destruct (seg_facts p v z Hpn Hvn Hz) as (Ep & Ev & Ew & _).
  pose proof (in_int_dist k z Hk Hint) as Dk. unfold ex in *.
  destruct (in_dec N.eq_dec k S) as [HkS | HkS].
  - pose proof (Hmin k v HkS Hvn HvS). pose proof (ex_tri k v z). unfold ex in *. lra.
  - pose proof (Hmin p k Hp Hk HkS). pose proof (ex_tri p k z). unfold ex in *. lra.
Qed.

Lemma in_int_self : forall k, (k < n)%N -> in_interior xs ys rs k (c k).
Proof.
  intros k Hk. unfold in_interior. pose proof (r_bounds k Hk).
  rewrite sqdist_eq. replace (radius rs k ^ 2) with (r k * r k) by ring. nra.
Qed.

Lemma apart_core : forall S T a b c' d,
  (forall s, In s T -> (s < n)%N) -> incl S T ->
  In a S -> ~ In b S -> (b < n)%N -> minp w n S a b ->
  In b T -> In c' T -> ~ In d T -> (d < n)%N -> minp w n T c' d ->
  forall z, seg_pts a b z -> seg_pts c' d z -> False.
Proof.
  intros S T a b c' d HT HST Ha Hb Hbn Hm1 HbT Hc HdT Hdn Hm2 z Z1 Z2.
  assert (Han : (a < n)%N) by auto. assert (Hcn : (c' < n)%N) by auto.
  assert (HaT : In a T) by auto.
  assert (HdS : ~ In d S) by auto.
  assert (Nab : a <> b) by (intros ->; contradiction).
  assert (Nad : a <> d) by (intros ->; contradiction).
  assert (Nbd : b <> d) by (intros ->; contradiction).
  assert (Ncd : c' <> d) by (intros ->; contradiction).
  pose proof (occl S a b Ha Hbn Hb Han Hm1) as O1.
  pose proof (occl T c' d Hc Hdn HdT Hcn Hm2) as O2.
  destruct (N.eq_dec b c') as [<- | Nbc].
  - (* the two beams leave the same dish b *)
    destruct (seg_facts b a z Hbn Han (seg_sym _ _ _ Z1)) as (_ & _ & _ & Rb & la & la0 & Ea).
    destruct (seg_facts b d z Hbn Hdn Z2) as (_ & _ & _ & _ & ld & ld0 & Ed).
    destruct (Rle_or_lt la ld) as [L | L].
    + apply (O2 a (c a) Han); [| apply in_int_self; exact Han].
      apply (ray b a d z la ld); auto; lra.
    + apply (O1 d (c d) Hdn); [| apply in_int_self; exact Hdn].
      apply seg_sym. apply (ray b d a z ld la); auto; lra.
  - destruct (seg_facts a b z Han Hbn Z1) as (A0 & B0 & Wab & Ra & lb & lb0 & Eb).
    destruct (seg_facts c' d z Hcn Hdn Z2) as (C0 & D0 & Wcd & Rc & ld & ld0 & Ed).
    pose proof (ex_tri a d z). pose proof (ex_tri b d z).
    pose proof (Hm2 a d HaT Hdn HdT). pose proof (Hm2 b d HbT Hdn HdT).
    pose proof (Hm1 a d Ha Hdn HdS).
    pose proof (r_bounds a Han). pose proof (r_bounds b Hbn).
    pose proof (r_bounds c' Hcn). pose proof (r_bounds d Hdn).
    destruct (in_dec N.eq_dec c' S) as [HcS | HcS].
    + pose proof (Hm1 c' b HcS Hbn Hb). pose proof (ex_tri c' b z).
      assert (Ncb : c' <> b) by (intros ->; contradiction).
      assert (Eq : dist (c c') (c b) = dist (c c') z + dist z (c b)).
      { rewrite (dist_sym z (c b)). unfold w, ex in *. lra. }
      pose proof (tri_eq _ _ _ Eq Rc) as Eb'.
      set (lb' := dist (c c') (c b) / dist (c c') z) in Eb'.
      assert (lb'0 : 0 <= lb').
      { unfold lb'. apply Rle_mult_inv_pos; [apply dist_nonneg | exact Rc]. }
      destruct (Rle_or_lt lb' ld) as [L | L].
      * apply (O2 b (c b) Hbn); [| apply in_int_self; exact Hbn].
        apply (ray c' b d z lb' ld); auto; lra.
      * pose proof (nov b d Hbn Hdn Nbd) as Nv.
        assert (Dbd : dist (c b) (c d) = (lb' - ld) * dist (c c') z).
        { rewrite Eb', Ed, dist_pt_pt, Rabs_right by lra. reflexivity. }
        assert (Dcb : dist (c c') (c b) = lb' * dist (c c') z).
        { rewrite Eb' at 1. rewrite <- (pt0 (c c') z) at 1. rewrite dist_pt_pt, Rminus_0_l, Rabs_Ropp.
          rewrite Rabs_right by lra. reflexivity. }
        assert (Dcd : dist (c c') (c d) = ld * dist (c c') z).
        { rewrite Ed. rewrite <- (pt0 (c c') z) at 1. rewrite dist_pt_pt, Rminus_0_l, Rabs_Ropp.
          rewrite Rabs_right by lra. reflexivity. }
        unfold w, ex in *. rewrite (dist_sym z (c b)) in Eq. lra.
    + pose proof (Hm1 a c' Ha Hcn HcS). pose proof (ex_tri a c' z).
      assert (Eq : dist (c a) (c c') = dist (c a) z + dist z (c c')).
      { rewrite (dist_sym z (c c')). unfold w, ex in *. lra. }
      pose proof (tri_eq _ _ _ Eq Ra) as Ec.
      set (lc := dist (c a) (c c') / dist (c a) z) in Ec.
      assert (lc0 : 0 <= lc).
      { unfold lc. apply Rle_mult_inv_pos; [apply dist_nonneg | exact Ra]. }
      pose proof (nov b c' Hbn Hcn Nbc) as Nv.
      assert (Dbc : dist (c b) (c c') = Rabs (lb - lc) * dist (c a) z).
      { rewrite Eb, Ec at 1. rewrite dist_pt_pt. reflexivity. }
      assert (Dab : dist (c a) (c b) = lb * dist (c a) z).
      { rewrite Eb at 1. rewrite <- (pt0 (c a) z) at 1. rewrite dist_pt_pt, Rminus_0_l, Rabs_Ropp.
        rewrite Rabs_right by lra. reflexivity. }
      assert (Dac : dist (c a) (c c') = lc * dist (c a) z).
      { rewrite Ec at 1. rewrite <- (pt0 (c a) z) at 1. rewrite dist_pt_pt, Rminus_0_l, Rabs_Ropp.
        rewrite Rabs_right by lra. reflexivity. }
      unfold w, ex in *. rewrite (dist_sym z (c c')) in Eq.
      destruct (Rle_or_lt lb lc) as [L | L].
      * rewrite Rabs_left1 in Dbc by lra. nra.
      * rewrite Rabs_right in Dbc by lra. nra.
Qed.

End Dish.

(* ================================================================== *)
(* Part 4. Prim's tree is a compliant design; every compliant design  *)
(* costs at least as much                                              *)
(* ================================================================== *)

Fixpoint insert_t (x : R * N) (l : list (R * N)) : list (R * N) :=
  match l with
  | [] => [x]
  | y :: l' => if Rle_dec (fst x) (fst y) then x :: y :: l' else y :: insert_t x l'
  end.

Definition le_t (a b : R * N) : Prop := fst a <= fst b.

Lemma insert_perm : forall x l, Permutation (x :: l) (insert_t x l).
Proof.
  intros x l; induction l as [| y l IH]; simpl; [auto |].
  destruct (Rle_dec (fst x) (fst y)); [auto |].
  eapply perm_trans; [apply perm_swap | constructor; exact IH].
Qed.

Lemma insert_hd : forall x y l, HdRel le_t y l -> fst y <= fst x -> HdRel le_t y (insert_t x l).
Proof.
  intros x y l H Hx. destruct l as [| z l]; simpl.
  - constructor. exact Hx.
  - destruct (Rle_dec (fst x) (fst z)); constructor; [exact Hx |]. inversion H; auto.
Qed.

Lemma insert_sorted : forall x l, Sorted le_t l -> Sorted le_t (insert_t x l).
Proof.
  intros x l; induction l as [| y l IH]; intros H; simpl.
  - constructor; constructor.
  - destruct (Rle_dec (fst x) (fst y)) as [L | L].
    + constructor; [exact H | constructor; exact L].
    + inversion H; subst. constructor; [apply IH; assumption |].
      apply insert_hd; [assumption | unfold le_t in *; lra].
Qed.

Lemma sort_exists : forall l : list (R * N), exists l', Permutation l l' /\ Sorted le_t l'.
Proof.
  intros l; induction l as [| x l (l' & P & S)].
  - exists []. split; constructor.
  - exists (insert_t x l'). split.
    + eapply perm_trans; [constructor; exact P | apply insert_perm].
    + apply insert_sorted, S.
Qed.

Lemma cfilter : forall {A} (P : A -> Prop) (L : list A), exists l, forall x, In x l <-> In x L /\ P x.
Proof.
  intros A P L; induction L as [| a L (l & Hl)].
  - exists []. simpl. tauto.
  - destruct (classic (P a)) as [Pa | Pa].
    + exists (a :: l). intros x. simpl. rewrite Hl. split.
      * intros [<- | H]; tauto.
      * intros [[<- | H] Px]; tauto.
    + exists l. intros x. simpl. rewrite Hl. split.
      * tauto.
      * intros [[<- | H] Px]; tauto.
Qed.

Fixpoint chain (l : list (R * N)) : list (N * N) :=
  match l with
  | a :: ((b :: _) as l') =>
      if N.eq_dec (snd a) (snd b) then chain l' else (snd a, snd b) :: chain l'
  | _ => []
  end.

Lemma costE_zero : forall W E, (forall e, In e E -> W (fst e) (snd e) = 0) -> costE W E = 0.
Proof.
  intros W E; induction E as [| e E IH]; intros H; simpl; [reflexivity |].
  rewrite H by (left; reflexivity). rewrite IH by (intros; apply H; right; auto). ring.
Qed.

Lemma crt_flat : forall (R1 R2 : N -> N -> Prop), (forall a b, R1 a b -> clos_refl_trans N R2 a b) ->
  forall a b, clos_refl_trans N R1 a b -> clos_refl_trans N R2 a b.
Proof.
  intros R1 R2 H a b C; induction C; [auto | apply rt_refl | eapply rt_trans; eauto].
Qed.

Lemma crt_edge_incl : forall E E' a b, incl E E' -> clos_refl_trans N (edge E) a b ->
  clos_refl_trans N (edge E') a b.
Proof.
  intros E E' a b H. apply crt_mono. intros x y [Hx | Hx]; [left | right]; apply H; exact Hx.
Qed.

Section Design.
Variables (xs ys : list Z) (rs : list N).
Hypothesis Hv : valid_input xs ys rs.

Local Notation n := (len xs).
Local Notation c := (centre xs ys).
Local Notation r := (radius rs).
Local Notation w := (w xs ys rs).

Definition beam_of (i j : N) : beam :=
  (pt (c i) (c j) (r i / dist (c i) (c j)), pt (c i) (c j) (1 - r j / dist (c i) (c j))).

Fixpoint design (steps : list (N * N)) : list beam :=
  match steps with
  | [] => []
  | (p, v) :: l => if Rlt_dec 0 (w p v) then beam_of p v :: design l else design l
  end.

Lemma D_pos : forall i j, (i < n)%N -> (j < n)%N -> 0 < w i j -> 0 < dist (c i) (c j).
Proof.
  intros i j Hi Hj H. pose proof (r_bounds xs ys rs Hv i Hi). pose proof (r_bounds xs ys rs Hv j Hj).
  rewrite (w_def xs ys rs) in H. lra.
Qed.

Lemma on_beam_seg : forall i j z, (i < n)%N -> (j < n)%N -> 0 < w i j ->
  on_beam (beam_of i j) z -> seg_pts xs ys rs i j z.
Proof.
  intros i j z Hi Hj Hw (t & Ht & ->).
  pose proof (D_pos i j Hi Hj Hw) as D0. rewrite (w_def xs ys rs) in Hw.
  set (D := dist (c i) (c j)) in *.
  exists (r i / D + t * (1 - r j / D - r i / D)). split; [| split].
  - unfold beam_of. fold D. destruct (c i) as [a b]. destruct (c j) as [a' b'].
    unfold pt; cbn [fst snd]. f_equal; field; lra.
  - fold D. replace ((r i / D + t * (1 - r j / D - r i / D)) * D) with (r i + t * (D - r j - r i))
      by (field; lra). nra.
  - fold D. replace ((r i / D + t * (1 - r j / D - r i / D)) * D) with (r i + t * (D - r j - r i))
      by (field; lra). nra.
Qed.

Lemma beam_length_of : forall i j, (i < n)%N -> (j < n)%N -> 0 < w i j ->
  beam_length (beam_of i j) = w i j.
Proof.
  intros i j Hi Hj Hw. pose proof (D_pos i j Hi Hj Hw) as D0.
  unfold beam_length, beam_of. cbn [fst snd]. fold (dist (pt (c i) (c j) (r i / dist (c i) (c j)))
    (pt (c i) (c j) (1 - r j / dist (c i) (c j)))).
  rewrite dist_pt_pt. rewrite ?(w_def xs ys rs) in *. set (D := dist (c i) (c j)) in *.
  rewrite Rabs_left1.
  - field. lra.
  - replace (r i / D - (1 - r j / D)) with ((r i + r j - D) / D) by (field; lra).
    unfold Rdiv. assert (0 < / D) by (apply Rinv_0_lt_compat; lra). nra.
Qed.

Lemma dist_end : forall i j s, 0 <= s -> dist (c i) (pt (c i) (c j) s) = s * dist (c i) (c j).
Proof.
  intros i j s Hs. rewrite <- (pt0 (c i) (c j)) at 1. rewrite dist_pt_pt, Rminus_0_l, Rabs_Ropp.
  rewrite Rabs_right by lra. reflexivity.
Qed.

Lemma sqdist_from_dist : forall p q d, 0 <= d -> dist q p = d -> sqdist p q = d ^ 2.
Proof.
  intros p q d Hd E. rewrite sqdist_sym, <- dist_sq, E. ring.
Qed.

Lemma ends_on : forall i j, (i < n)%N -> (j < n)%N -> 0 < w i j ->
  on_circle xs ys rs i (fst (beam_of i j)) /\ on_circle xs ys rs j (snd (beam_of i j)).
Proof.
  intros i j Hi Hj Hw. pose proof (D_pos i j Hi Hj Hw) as D0.
  pose proof (r_bounds xs ys rs Hv i Hi). pose proof (r_bounds xs ys rs Hv j Hj).
  rewrite (w_def xs ys rs) in Hw. unfold on_circle, beam_of. cbn [fst snd]. split.
  - apply sqdist_from_dist; [lra |]. rewrite dist_end.
    + field. lra.
    + apply Rle_mult_inv_pos; lra.
  - apply sqdist_from_dist; [lra |].
    rewrite <- (pt1 (c i) (c j)) at 1. rewrite dist_pt_pt.
    rewrite Rabs_right.
    + field. lra.
    + replace (1 - (1 - r j / dist (c i) (c j))) with (r j / dist (c i) (c j)) by ring.
      apply Rle_ge, Rle_mult_inv_pos; lra.
Qed.

Lemma meets_ends : forall i j, (i < n)%N -> (j < n)%N -> 0 < w i j ->
  meets xs ys rs (beam_of i j) i /\ meets xs ys rs (beam_of i j) j.
Proof.
  intros i j Hi Hj Hw. destruct (ends_on i j Hi Hj Hw) as [E1 E2]. split.
  - exists (fst (beam_of i j)). split; [| unfold on_circle in E1; lra].
    exists 0. split; [lra |]. destruct (beam_of i j) as [[a b] q]. cbn [fst snd]. f_equal; ring.
  - exists (snd (beam_of i j)). split; [| unfold on_circle in E2; lra].
    exists 1. split; [lra |]. destruct (beam_of i j) as [[a b] [a' b']]. cbn [fst snd]. f_equal; ring.
Qed.

Lemma In_design : forall steps b, In b (design steps) ->
  exists p v, In (p, v) steps /\ 0 < w p v /\ b = beam_of p v.
Proof.
  intros steps b; induction steps as [| [p v] steps IH]; simpl; [tauto |].
  destruct (Rlt_dec 0 (w p v)) as [H | H].
  - intros [<- | Hb]; [exists p, v; auto |].
    destruct (IH Hb) as (p' & v' & ?& ? & ?). exists p', v'. auto.
  - intros Hb. destruct (IH Hb) as (p' & v' & ?& ? & ?). exists p', v'. auto.
Qed.

Lemma design_In : forall steps p v, In (p, v) steps -> 0 < w p v -> In (beam_of p v) (design steps).
Proof.
  intros steps p v; induction steps as [| [p' v'] steps IH]; simpl; [tauto |].
  intros [E | H] Hw.
  - inversion E; subst. destruct (Rlt_dec 0 (w p v)); [left; reflexivity | contradiction].
  - destruct (Rlt_dec 0 (w p' v')); [right |]; auto.
Qed.

Lemma Forall_design : forall (P : beam -> Prop) steps,
  (forall p v, In (p, v) steps -> 0 < w p v -> P (beam_of p v)) -> Forall P (design steps).
Proof.
  intros P steps H. apply Forall_forall. intros b Hb.
  destruct (In_design steps b Hb) as (p & v & H1 & H2 & ->). auto.
Qed.

Lemma total_design : forall steps, Forall (okedge n) steps ->
  total_length (design steps) = costE w steps.
Proof.
  intros steps; induction steps as [| [p v] steps IH]; intros H; simpl; [reflexivity |].
  inversion H as [| e l He Hl]; subst. destruct He as (H1 & H2 & H3); cbn [fst snd] in *.
  destruct (Rlt_dec 0 (w p v)) as [L | L].
  - simpl. rewrite beam_length_of by assumption. rewrite IH by assumption. reflexivity.
  - pose proof (w_nonneg xs ys rs Hv p v H1 H2 H3). rewrite IH by assumption. lra.
Qed.

Lemma run_later_range : forall W S steps S', run W n S steps S' -> (forall s, In s S -> (s < n)%N) ->
  forall c' d, In (c', d) steps -> exists T, incl S T /\ (forall s, In s T -> (s < n)%N) /\
    In c' T /\ ~ In d T /\ (d < n)%N /\ minp W n T c' d.
Proof.
  intros W S steps S' R; induction R as [S | S p v steps S' Hp Hvn HvS Hmin R IH];
    intros HS c' d Hin; [destruct Hin |].
  destruct Hin as [E | Hin].
  - inversion E; subst. exists S. repeat split; auto. apply incl_refl.
  - destruct (IH ltac:(intros s [<- | Hs]; auto) c' d Hin) as (T & HT & HTr & H1 & H2 & H3 & H4).
    exists T. repeat split; auto. intros x Hx. apply HT. right. exact Hx.
Qed.

Lemma design_compliant_parts : forall S steps S', run w n S steps S' ->
  (forall s, In s S -> (s < n)%N) ->
  Forall (joins_two_dishes xs ys rs) (design steps) /\
  ForallOrdPairs apart (design steps) /\
  Forall (occludes_no_dish xs ys rs) (design steps).
Proof.
  intros S steps S' R; induction R as [S | S p v steps S' Hp Hvn HvS Hmin R IH]; intros HS.
  - simpl. repeat split; constructor.
  - assert (HS' : forall s, In s (v :: S) -> (s < n)%N) by (intros s [<- | Hs]; auto).
    destruct (IH HS') as (J & A & O).
    assert (Hpn : (p < n)%N) by auto.
    assert (Npv : p <> v) by (intros ->; contradiction).
    simpl. destruct (Rlt_dec 0 (w p v)) as [Hw | Hw]; [| auto].
    repeat split.
    + constructor; [| exact J]. exists p, v. repeat split; auto; apply ends_on; auto.
    + constructor; [| exact A]. apply Forall_design. intros c' d Hin Hw'.
      destruct (run_later_range w (v :: S) steps S' R HS' c' d Hin)
        as (T & HT & HTr & HcT & HdT & Hdn & Hm).
      assert (Hcn : (c' < n)%N) by auto.
      intros z Z1 Z2.
      apply (apart_core xs ys rs Hv S T p v c' d HTr (fun x Hx => HT x (or_intror Hx)) Hp HvS Hvn Hmin
               (HT v (or_introl eq_refl)) HcT HdT Hdn Hm z).
      * apply on_beam_seg; auto.
      * apply on_beam_seg; auto.
    + constructor; [| exact O]. intros k z Hk Hz Hint.
      apply (occl xs ys rs Hv S p v Hp Hvn HvS Hpn Hmin k z Hk); [| exact Hint].
      apply on_beam_seg; auto.
Qed.

Lemma linked_sym : forall d i j, linked xs ys rs d i j -> linked xs ys rs d j i.
Proof.
  intros d i j (Hi & Hj & [(N1 & T) | (b & Hb & M1 & M2)]); split; auto; split; auto.
  - left. split; [auto |]. rewrite sqdist_sym, T. ring.
  - right. exists b. auto.
Qed.

Lemma step_linked : forall steps p v, In (p, v) steps -> okedge n (p, v) ->
  linked xs ys rs (design steps) p v.
Proof.
  intros steps p v Hin (Hp & Hvn & Npv). cbn [fst snd] in *.
  split; [exact Hp |]. split; [exact Hvn |].
  destruct (Rlt_dec 0 (w p v)) as [Hw | Hw].
  - right. exists (beam_of p v). split; [apply design_In; auto |]. apply meets_ends; auto.
  - left. split; [exact Npv |]. pose proof (w_nonneg xs ys rs Hv p v Hp Hvn Npv).
    rewrite ?(w_def xs ys rs) in *. apply sqdist_from_dist.
    + pose proof (r_bounds xs ys rs Hv p Hp). pose proof (r_bounds xs ys rs Hv v Hvn). lra.
    + rewrite dist_sym. lra.
Qed.

Lemma design_connected : forall steps S', run w n [0%N] steps S' -> (0 < n)%N ->
  (forall x, (x < n)%N -> In x S') -> connected xs ys rs (design steps).
Proof.
  intros steps S' R H0 All.
  destruct (run_ok w n _ _ _ R ltac:(intros s [<- | []]; exact H0)) as [Ok _].
  assert (L : forall a b, edge steps a b -> linked xs ys rs (design steps) a b).
  { intros a b [H | H].
    - apply step_linked; auto. rewrite Forall_forall in Ok. auto.
    - apply linked_sym, step_linked; auto. rewrite Forall_forall in Ok. auto. }
  assert (C0 : forall x, (x < n)%N -> clos_refl_trans N (linked xs ys rs (design steps)) x 0%N).
  { intros x Hx. destruct (run_conn w n _ _ _ R x (All x Hx)) as (s & [<- | []] & C).
    eapply crt_mono; [exact L | exact C]. }
  intros i j Hi Hj. eapply rt_trans; [apply C0; exact Hi |].
  apply crt_sym; [apply linked_sym | apply C0; exact Hj].
Qed.

(* ---------------- the lower bound ---------------- *)

Lemma w_le_points : forall i j zi zj, (i < n)%N -> (j < n)%N ->
  sqdist zi (c i) <= r i ^ 2 -> sqdist zj (c j) <= r j ^ 2 -> w i j <= dist zi zj.
Proof.
  intros i j zi zj Hi Hj H1 H2.
  pose proof (r_bounds xs ys rs Hv i Hi). pose proof (r_bounds xs ys rs Hv j Hj).
  assert (D1 : dist (c i) zi <= r i).
  { unfold dist. rewrite sqdist_sym. apply sqrt_le_bound; [lra |]. replace (r i * r i) with (r i ^ 2) by ring. exact H1. }
  assert (D2 : dist zj (c j) <= r j).
  { unfold dist. apply sqrt_le_bound; [lra |]. replace (r j * r j) with (r j ^ 2) by ring. exact H2. }
  pose proof (dist_tri (c i) zi (c j)). pose proof (dist_tri zi zj (c j)).
  rewrite (w_def xs ys rs). lra.
Qed.

Definition good_t (b : beam) (ti : R * N) : Prop :=
  0 <= fst ti <= 1 /\ (snd ti < n)%N /\
  sqdist (pt (fst b) (snd b) (fst ti)) (c (snd ti)) <= r (snd ti) ^ 2.

Lemma chain_cost : forall b l a, Sorted le_t (a :: l) -> Forall (good_t b) (a :: l) ->
  costE w (chain (a :: l)) <= (1 - fst a) * beam_length b.
Proof.
  intros b l; induction l as [| a' l IH]; intros a Hs Hg.
  - simpl. inversion Hg as [| ? ? (G1 & _) _]; subst.
    pose proof (sqrt_pos (sqdist (fst b) (snd b))). unfold beam_length. nra.
  - inversion Hs as [| ? ? Hs' Hhd]; subst. inversion Hhd as [| ? ? Hle]; subst.
    inversion Hg as [| ? ? Ga Hg']; subst. inversion Hg' as [| ? ? Ga' _]; subst.
    specialize (IH a' Hs' Hg').
    destruct Ga as (Ta & Ia & Pa). destruct Ga' as (Ta' & Ia' & Pa').
    unfold le_t in Hle.
    assert (L0 : 0 <= beam_length b) by apply sqrt_pos.
    change (chain (a :: a' :: l)) with
      (if N.eq_dec (snd a) (snd a') then chain (a' :: l) else (snd a, snd a') :: chain (a' :: l)).
    destruct (N.eq_dec (snd a) (snd a')) as [E | E].
    + nra.
    + change (costE w ((snd a, snd a') :: chain (a' :: l))) with
        (w (snd a) (snd a') + costE w (chain (a' :: l))).
      pose proof (w_le_points _ _ _ _ Ia Ia' Pa Pa') as Wl.
      rewrite dist_pt_pt, Rabs_left1 in Wl by lra.
      change (dist (fst b) (snd b)) with (beam_length b) in Wl. nra.
Qed.

Lemma chain_ok : forall b l, Forall (good_t b) l -> Forall (okedge n) (chain l).
Proof.
  intros b l; induction l as [| a l IH]; intros H; [constructor |].
  destruct l as [| a' l]; [constructor |].
  inversion H as [| ? ? Ga Hg]; subst. inversion Hg as [| ? ? Ga' _]; subst.
  change (chain (a :: a' :: l)) with
    (if N.eq_dec (snd a) (snd a') then chain (a' :: l) else (snd a, snd a') :: chain (a' :: l)).
  destruct (N.eq_dec (snd a) (snd a')) as [E | E]; [auto |].
  constructor; [| auto]. destruct Ga as (_ & ? & _). destruct Ga' as (_ & ? & _).
  repeat split; auto.
Qed.

Lemma chain_conn : forall l a x, In x (a :: l) ->
  clos_refl_trans N (edge (chain (a :: l))) (snd a) (snd x).
Proof.
  intros l; induction l as [| a' l IH]; intros a x Hx.
  - destruct Hx as [<- | []]. apply rt_refl.
  - change (chain (a :: a' :: l)) with
      (if N.eq_dec (snd a) (snd a') then chain (a' :: l) else (snd a, snd a') :: chain (a' :: l)).
    destruct Hx as [<- | Hx]; [apply rt_refl |].
    specialize (IH a' x Hx).
    destruct (N.eq_dec (snd a) (snd a')) as [E | E].
    + rewrite E. exact IH.
    + eapply rt_trans; [apply rt_step; left; left; reflexivity |].
      eapply crt_edge_incl; [| exact IH]. intros e He. right. exact He.
Qed.

Lemma beam_list : forall b (L : list N), (forall i, In i L -> (i < n)%N) ->
  exists l, Forall (good_t b) l /\
    forall i, In i L -> meets xs ys rs b i -> exists t, In (t, i) l.
Proof.
  intros b L; induction L as [| i L IH]; intros HL.
  - exists []. split; [constructor | intros i []].
  - destruct (IH (fun j Hj => HL j (or_intror Hj))) as (l & G & M).
    destruct (classic (meets xs ys rs b i)) as [Mi | Mi].
    + destruct Mi as (z & (t & Ht & Ez) & Hz).
      exists ((t, i) :: l). split.
      * constructor; [| exact G]. split; [exact Ht |]. split; [apply HL; left; auto |].
        cbn [fst snd]. replace (pt (fst b) (snd b) t) with z by (rewrite Ez; reflexivity). exact Hz.
      * intros j [<- | Hj] Mj; [exists t; left; reflexivity |].
        destruct (M j Hj Mj) as (t' & H'). exists t'. right. exact H'.
    + exists l. split; [exact G |]. intros j [<- | Hj] Mj; [contradiction | auto].
Qed.

Lemma beams_edges : forall d, exists E, Forall (okedge n) E /\ costE w E <= total_length d /\
  forall b i j, In b d -> (i < n)%N -> (j < n)%N -> meets xs ys rs b i -> meets xs ys rs b j ->
    clos_refl_trans N (edge E) i j.
Proof.
  intros d; induction d as [| b d (E & Ok & Co & Cn)].
  - exists []. split; [constructor |]. split; [simpl; lra | intros b i j []].
  - destruct (beam_list b (verts n) (fun i Hi => proj1 (verts_In n i) Hi)) as (l & G & M).
    destruct (sort_exists l) as (l' & P & Srt).
    assert (G' : Forall (good_t b) l') by (eapply Permutation_Forall; eassumption).
    destruct l' as [| a l''].
    + exists E. split; [exact Ok |]. split.
      * simpl. pose proof (sqrt_pos (sqdist (fst b) (snd b))). unfold beam_length in *. lra.
      * intros b' i j [<- | Hb'] Hi Hj Mi Mj; [| apply (Cn b'); auto].
        destruct (M i (proj2 (verts_In n i) Hi) Mi) as (t & Ht).
        apply (Permutation_in _ P) in Ht. destruct Ht.
    + exists (chain (a :: l'') ++ E). split; [apply Forall_app; split; [eapply chain_ok; eauto | exact Ok] |].
      split.
      * rewrite costE_app. simpl total_length. pose proof (chain_cost b l'' a Srt G').
        inversion G' as [| ? ? (Ta & _) _]; subst. pose proof (sqrt_pos (sqdist (fst b) (snd b))).
        unfold beam_length in *. nra.
      * intros b' i j [<- | Hb'] Hi Hj Mi Mj.
        -- destruct (M i (proj2 (verts_In n i) Hi) Mi) as (t & Ht).
           destruct (M j (proj2 (verts_In n j) Hj) Mj) as (t' & Ht').
           apply (Permutation_in _ P) in Ht, Ht'.
           apply (crt_edge_incl (chain (a :: l''))); [intros e He; apply in_or_app; left; exact He |].
           eapply rt_trans; [apply crt_edge_sym, (chain_conn l'' a (t, i) Ht) |].
           apply (chain_conn l'' a (t', j) Ht').
        -- apply (crt_edge_incl E); [intros e He; apply in_or_app; right; exact He |]. apply (Cn b'); auto.
Qed.

Lemma touch_edges : exists E, Forall (okedge n) E /\ costE w E = 0 /\
  forall i j, (i < n)%N -> (j < n)%N -> touch xs ys rs i j -> In (i, j) E.
Proof.
  destruct (cfilter (fun e => touch xs ys rs (fst e) (snd e)) (list_prod (verts n) (verts n)))
    as (E & HE).
  exists E. split; [| split].
  - apply Forall_forall. intros [i j] H. apply HE in H as [H (N1 & _)].
    apply in_prod_iff in H as [H1 H2]. apply verts_In in H1, H2. repeat split; auto.
  - apply costE_zero. intros [i j] H. apply HE in H as [H (N1 & T)].
    apply in_prod_iff in H as [H1 H2]. apply verts_In in H1, H2. cbn [fst snd] in *.
    pose proof (r_bounds xs ys rs Hv i H1). pose proof (r_bounds xs ys rs Hv j H2).
    rewrite (w_def xs ys rs). unfold dist. rewrite T. rewrite sqrt_pow2 by lra. ring.
  - intros i j Hi Hj T. apply HE. split; [apply in_prod; apply verts_In; auto | exact T].
Qed.

Lemma lower_bound : forall W' steps S', run W' n [0%N] steps S' ->
  (forall i j, W' i j = W' j i) -> (forall i j, (i < n)%N -> (j < n)%N -> i <> j -> 0 <= W' i j) ->
  (forall i j, (i < n)%N -> (j < n)%N -> i <> j -> W' i j <= w i j) ->
  forall d, compliant xs ys rs d -> costE W' steps <= total_length d.
Proof.
  intros W' steps S' R Ws Wn Wle d (_ & _ & _ & Conn).
  destruct touch_edges as (E1 & Ok1 & Co1 & T1).
  destruct (beams_edges d) as (E2 & Ok2 & Co2 & B2).
  assert (Ok : Forall (okedge n) (E1 ++ E2)) by (apply Forall_app; auto).
  assert (Lk : forall i j, linked xs ys rs d i j -> clos_refl_trans N (edge (E1 ++ E2)) i j).
  { intros i j (Hi & Hj & [T | (b & Hb & Mi & Mj)]).
    - apply rt_step. left. apply in_or_app. left. apply T1; auto.
    - apply (crt_edge_incl E2); [intros e He; apply in_or_app; right; exact He |]. eauto. }
  pose proof (vi_n _ _ _ Hv) as Hn.
  assert (Cn : forall x, (x < n)%N -> exists s, In s [0%N] /\ clos_refl_trans N (edge (E1 ++ E2)) x s).
  { intros x Hx. exists 0%N. split; [left; reflexivity |].
    eapply crt_flat; [exact Lk |]. apply Conn; unfold is_dish; lia. }
  pose proof (prim_lower W' n Ws Wn _ _ _ R _ Ok Cn) as L.
  assert (L2 : costE W' (E1 ++ E2) <= costE w (E1 ++ E2)).
  { clear - Ok Wle. induction (E1 ++ E2) as [| e E IH]; simpl; [lra |].
    inversion Ok as [| ? ? (H1 & H2 & H3) Ok']; subst. specialize (IH Ok').
    pose proof (Wle _ _ H1 H2 H3). lra. }
  rewrite !costE_app in L2, L. rewrite (costE_app w E1 E2) in L2. lra.
Qed.

End Design.

(* the exact optimum : Prim's tree on the exact weights *)
Lemma exact_min : forall xs ys rs, valid_input xs ys rs ->
  exists steps S', run (w xs ys rs) (len xs) [0%N] steps S' /\
    (forall x, (x < len xs)%N -> In x S') /\
    minimum_cost xs ys rs (costE (w xs ys rs) steps).
Proof.
  intros xs ys rs Hv. pose proof (vi_n _ _ _ Hv) as Hn.
  destruct (run_exists (w xs ys rs) (len xs) [0%N]) as (steps & S' & R & All).
  - intros s [<- | []]. lia.
  - discriminate.
  - constructor; [intros [] | constructor].
  - exists steps, S'. split; [exact R |]. split; [exact All |].
    destruct (run_ok _ _ _ _ _ R ltac:(intros s [<- | []]; lia)) as [Ok _].
    split.
    + exists (design xs ys rs steps).
      destruct (design_compliant_parts xs ys rs Hv _ _ _ R ltac:(intros s [<- | []]; lia))
        as (J & A & O).
      split; [| apply total_design; auto].
      repeat split; auto. apply (design_connected xs ys rs Hv steps S'); auto. lia.
    + intros d Hd. apply (lower_bound xs ys rs Hv (w xs ys rs) steps S' R).
      * apply w_sym.
      * apply (w_nonneg xs ys rs Hv).
      * intros; lra.
      * exact Hd.
Qed.

Close Scope R_scope.

(* ================================================================== *)
(* Part 5. The program                                                 *)
(* ================================================================== *)

Open Scope uint63_scope.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

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

Section Loop.
Context {St : Type}.

Fixpoint wloop (hi : int) (f : int -> St -> St)
    (i : int) (s : St) (H : Acc (Zwf 0) (gap hi i)) {struct H} : St :=
  match bdec (i <? hi) with
  | left Hi => wloop hi f (i + 1) (f i s) (Acc_inv H (dec_step hi i Hi))
  | right _ => s
  end.

(* for i = lo, lo+1, ..., hi-1 : s := f i s *)
Definition loop (hi : int) (f : int -> St -> St) (i : int) (s : St) : St :=
  wloop hi f i s (Zwf_well_founded 0 (gap hi i)).

End Loop.

(* the squared distance of the centres of dishes i and j, exact in int *)
Definition dsq (x y : array sint) (i j : int) : int :=
  let dx := x.[i] - x.[j] in
  let dy := y.[i] - y.[j] in
  dx * dx + dy * dy.

(* the weight of the edge i j : the gap between the two dishes *)
Definition wt (x y : array sint) (r : array uint) (i j : int) : float :=
  (PrimFloat.sqrt (of_uint63 (dsq x y i j)) - of_uint63 (r.[i] + r.[j]))%float.

Definition init_step (x y : array sint) (r : array uint) (v : int) (key : array float) : array float :=
  key.[v <- wt x y r 0 v].

(* the argmin of key over the dishes not in the tree ; n is "none yet" *)
Definition amin_step (n : int) (inT : array bool) (key : array float) (v : int) (st : int * float)
    : int * float :=
  let '(b, bv) := st in
  if inT.[v] then st
  else if b =? n then (v, key.[v])
  else if (key.[v] <? bv)%float then (v, key.[v]) else st.

(* dish b joined the tree : update the keys of the others *)
Definition upd_step (x y : array sint) (r : array uint) (inT : array bool) (b : int)
    (v : int) (key : array float) : array float :=
  if inT.[v] then key
  else
    let wv := wt x y r b v in
    if (wv <? key.[v])%float then key.[v <- wv] else key.

Definition prim_step (x y : array sint) (r : array uint) (n : int) (k : int)
    (st : array bool * array float * float) : array bool * array float * float :=
  let '(inT, key, tot) := st in
  let '(b, _) := loop n (amin_step n inT key) 0 (n, PrimFloat.zero) in
  let tot := (tot + key.[b])%float in
  let inT := inT.[b <- true] in
  let key := loop n (upd_step x y r inT b) 0 key in
  (inT, key, tot).

Definition comsat (x y : array sint) (r : array uint) : float :=
  let n := PArray.length x in
  let inT := (PArray.make n false).[0 <- true] in
  let key := loop n (init_step x y r) 0 (PArray.make n PrimFloat.zero) in
  let '(_, _, tot) := loop n (prim_step x y r n) 1 (inT, key, PrimFloat.zero) in
  tot.

(* ================================================================== *)
(* Part 6. Proof of the program                                        *)
(* ================================================================== *)

Section LoopProof.
Context {St : Type}.

Lemma wloop_eq : forall (hi : int) (f : int -> St -> St) i s H,
  wloop hi f i s H =
  match bdec (i <? hi) with
  | left Hi => wloop hi f (i + 1) (f i s) (Acc_inv H (dec_step hi i Hi))
  | right _ => s
  end.
Proof. intros. destruct H; reflexivity. Qed.

Lemma for_inv : forall (P : int -> St -> Prop) (hi lo : int) f s,
  (to_Z lo <= to_Z hi)%Z -> P lo s ->
  (forall j t, (to_Z lo <= to_Z j < to_Z hi)%Z -> P j t -> P (j + 1) (f j t)) ->
  P hi (loop hi f lo s).
Proof.
  intros P hi lo f s Hle Hp Hstep. unfold loop.
  assert (G : forall m i t (H : Acc (Zwf 0) (gap hi i)), gap hi i = m ->
     (to_Z lo <= to_Z i <= to_Z hi)%Z -> P i t -> P hi (wloop hi f i t H)).
  { intros m. induction m as [m IH] using (well_founded_induction (Zwf_well_founded 0)).
    intros i t H Em Hi Pt. rewrite wloop_eq. destruct (bdec (i <? hi)) as [Hlt | Hge].
    - pose proof Hlt as Hlt'. rewrite Uint63.ltb_spec in Hlt'.
      apply (IH (gap hi (i + 1))).
      + rewrite <- Em. apply dec_step; exact Hlt.
      + reflexivity.
      + pose proof (to_Z_bounded hi). assert (to_Z (i + 1) = (to_Z i + 1)%Z) by sia. lia.
      + apply Hstep; auto; lia.
    - assert (~ (to_Z i < to_Z hi)%Z) by (rewrite <- Uint63.ltb_spec; congruence).
      assert (i = hi) by (apply to_Z_inj; lia). subst. exact Pt. }
  apply (G _ lo s _ eq_refl); [lia | exact Hp].
Qed.

End LoopProof.

Lemma succ_spec : forall j hi : int, (to_Z j < to_Z hi)%Z -> to_Z (j + 1) = (to_Z j + 1)%Z.
Proof. intros j hi H. pose proof (to_Z_bounded hi). sia. Qed.

Lemma lt_succ : forall j hi v : int, (to_Z j < to_Z hi)%Z ->
  (to_Z v < to_Z (j + 1))%Z -> (to_Z v < to_Z j)%Z \/ v = j.
Proof.
  intros j hi v H Hv. rewrite (succ_spec j hi H) in Hv.
  destruct (Z.lt_ge_cases (to_Z v) (to_Z j)); [left; auto | right; apply to_Z_inj; lia].
Qed.

(* PArray, restated at the element types of the program *)
Lemma bget_set_same : forall (t : array bool) (i : int) v,
  (i <? PArray.length t) = true -> t.[i <- v].[i] = v.
Proof. intros t i v H. exact (get_set_same bool t i v H). Qed.
Lemma bget_set_other : forall (t : array bool) (i j : int) v, i <> j -> t.[i <- v].[j] = t.[j].
Proof. intros t i j v H. exact (get_set_other bool t i j v H). Qed.
Lemma blength_set : forall (t : array bool) (i : int) v, PArray.length t.[i <- v] = PArray.length t.
Proof. intros. exact (length_set bool t i v). Qed.
Lemma fget_set_same : forall (t : array float) (i : int) v,
  (i <? PArray.length t) = true -> t.[i <- v].[i] = v.
Proof. intros t i v H. exact (get_set_same float t i v H). Qed.
Lemma fget_set_other : forall (t : array float) (i j : int) v, i <> j -> t.[i <- v].[j] = t.[j].
Proof. intros t i j v H. exact (get_set_other float t i j v H). Qed.
Lemma flength_set : forall (t : array float) (i : int) v, PArray.length t.[i <- v] = PArray.length t.
Proof. intros. exact (length_set float t i v). Qed.

Lemma blength_make : forall (n : int) (v : bool),
  PArray.length (PArray.make n v) = if (n <=? max_length)%uint63 then n else max_length.
Proof. intros n v. exact (length_make bool n v). Qed.
Lemma flength_make : forall (n : int) (v : float),
  PArray.length (PArray.make n v) = if (n <=? max_length)%uint63 then n else max_length.
Proof. intros n v. exact (length_make float n v). Qed.
Lemma bget_make : forall (n i : int) (v : bool), (PArray.make n v).[i] = v.
Proof. intros n i v. exact (get_make bool v n i). Qed.

Close Scope uint63_scope.
Open Scope R_scope.

Lemma rnd_err : forall z, Rabs (rnd z - z) <= Rabs z * (u / 2) + u / 2.
Proof.
  intros z. destruct (rnd_model z) as (eps & eta & He & Ht & _ & ->).
  replace (z * (1 + eps) + eta - z) with (z * eps + eta) by ring.
  eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_mult.
  pose proof eta_max_le_u. pose proof (Rabs_pos z).
  assert (Rabs z * Rabs eps <= Rabs z * (u / 2)) by (apply Rmult_le_compat_l; lra).
  lra.
Qed.

Lemma bpow_big : 1000000000000 <= Raux.bpow Zaux.radix2 1000.
Proof.
  pose proof (Raux.bpow_le Zaux.radix2 40 1000 ltac:(lia)) as H.
  change (Raux.bpow Zaux.radix2 40) with 1099511627776 in H. lra.
Qed.

Lemma no_ovf : forall z, Rabs z <= 1000000000000 -> Rabs (rnd z) < Raux.bpow Zaux.radix2 1024.
Proof. intros z H. apply rnd_no_overflow_small. pose proof bpow_big. lra. Qed.

Lemma repr_zero : repr PrimFloat.zero 0.
Proof. split; reflexivity. Qed.

Lemma acc_err : forall vt cc a K, 0 <= cc -> 0 <= a -> 0 <= K <= 2000 ->
  Rabs (vt - cc) <= K * u * (cc + 1) ->
  Rabs (rnd (vt + a) - (cc + a)) <= (K + 1) * u * (cc + a + 1).
Proof.
  intros vt cc a K Hc Ha HK H.
  pose proof (rnd_err (vt + a)) as E. pose proof u_pos as U.
  assert (Uv : u <= / 1000000) by (rewrite u_val; lra).
  set (X := cc + a + 1).
  assert (H' : Rabs (vt - cc) <= K * u * X).
  { eapply Rle_trans; [exact H |]. apply Rmult_le_compat_l; [nra | unfold X; lra]. }
  assert (Z : Rabs (vt + a) <= X - 1 + K * u * X).
  { replace (vt + a) with ((vt - cc) + (cc + a)) by ring.
    eapply Rle_trans; [apply Rabs_triang |]. rewrite (Rabs_right (cc + a)) by lra. unfold X in *. lra. }
  replace (rnd (vt + a) - (cc + a)) with ((rnd (vt + a) - (vt + a)) + (vt - cc)) by ring.
  eapply Rle_trans; [apply Rabs_triang |].
  assert (KU : K * u <= 1) by nra.
  assert (X0 : 1 <= X) by (unfold X; lra).
  assert (T : Rabs (vt + a) * (u / 2) <= (X - 1 + K * u * X) * (u / 2)) by (apply Rmult_le_compat_r; lra).
  assert (T2 : K * u * X * (u / 2) <= X * (u / 2)).
  { replace (K * u * X * (u / 2)) with ((K * u) * (X * (u / 2))) by ring.
    assert (0 <= X * (u / 2)) by nra. nra. }
  replace ((K + 1) * u * X) with (K * u * X + X * (u / 2) + X * (u / 2)) by field.
  lra.
Qed.

Section Mach.
Variables (xs ys : list Z) (rs : list N) (x y : array sint) (r : array uint).
Hypothesis Hv : valid_input xs ys rs.
Hypothesis Hx : repr x xs.
Hypothesis Hy : repr y ys.
Hypothesis Hr : repr r rs.

Local Notation nI := (PArray.length x).
Local Notation nN := (len xs).

Definition toN (a : int) : N := Z.to_N (to_Z a).
Definition XX (i : N) : Z := nth (N.to_nat i) xs 0%Z.
Definition YY (i : N) : Z := nth (N.to_nat i) ys 0%Z.
Definition RR (i : N) : N := nth (N.to_nat i) rs 0%N.
Definition D2 (i j : N) : Z := ((XX i - XX j) * (XX i - XX j) + (YY i - YY j) * (YY i - YY j))%Z.

(* the weight the program computes, as a real *)
Definition Wh (i j : N) : R := rnd (rnd (sqrt (IZR (D2 i j))) - IZR (Z.of_N (RR i + RR j))).

Lemma lenx : Z.of_nat (List.length xs) = to_Z nI.
Proof. exact (proj1 Hx). Qed.

Lemma nI_eq : to_Z nI = Z.of_N nN.
Proof. rewrite <- lenx. unfold len. lia. Qed.

Lemma n_bounds : (1 <= to_Z nI <= 2000)%Z.
Proof. rewrite nI_eq. pose proof (vi_n _ _ _ Hv). lia. Qed.

Lemma len_ys : List.length ys = List.length xs.
Proof. pose proof (vi_len_ys _ _ _ Hv) as E. unfold len in E. lia. Qed.

Lemma len_rs : List.length rs = List.length xs.
Proof. pose proof (vi_len_rs _ _ _ Hv) as E. unfold len in E. lia. Qed.

Lemma toN_lt : forall a, (to_Z a < to_Z nI)%Z -> (toN a < nN)%N.
Proof. intros a H. unfold toN. rewrite nI_eq in H. pose proof (to_Z_bounded a). lia. Qed.

Lemma toN_inj : forall a b, toN a = toN b -> a = b.
Proof.
  intros a b H. unfold toN in H. pose proof (to_Z_bounded a). pose proof (to_Z_bounded b).
  apply to_Z_inj. lia.
Qed.

Definition ofN (i : N) : int := of_Z (Z.of_N i).

Lemma ofN_spec : forall i, (i < nN)%N -> to_Z (ofN i) = Z.of_N i /\ toN (ofN i) = i.
Proof.
  intros i Hi. pose proof n_bounds. rewrite nI_eq in H.
  assert (E : to_Z (ofN i) = Z.of_N i).
  { unfold ofN. rewrite of_Z_spec. apply Z.mod_small. change wB with (2 ^ 63)%Z. lia. }
  split; [exact E | unfold toN; rewrite E; lia].
Qed.

Lemma XX_get : forall a, (to_Z a < to_Z nI)%Z -> Sint63.to_Z x.[a] = XX (toN a).
Proof.
  intros a Ha. unfold XX, toN. rewrite Z_N_nat. pose proof lenx. destruct Hx as [L0 HH].
  destruct (HH (Z.to_nat (to_Z a)) ltac:(lia)) as (m & E & R).
  rewrite (nth_error_nth _ _ _ E). rewrite Z2Nat.id in R by (pose proof (to_Z_bounded a); lia).
  rewrite of_to_Z in R. exact R.
Qed.

Lemma YY_get : forall a, (to_Z a < to_Z nI)%Z -> Sint63.to_Z y.[a] = YY (toN a).
Proof.
  intros a Ha. unfold YY, toN. rewrite Z_N_nat. pose proof len_ys. pose proof lenx. destruct Hy as [L0 HH].
  destruct (HH (Z.to_nat (to_Z a)) ltac:(lia)) as (m & E & R).
  rewrite (nth_error_nth _ _ _ E). rewrite Z2Nat.id in R by (pose proof (to_Z_bounded a); lia).
  rewrite of_to_Z in R. exact R.
Qed.

Lemma RR_get : forall a, (to_Z a < to_Z nI)%Z -> to_Z r.[a] = Z.of_N (RR (toN a)).
Proof.
  intros a Ha. unfold RR, toN. rewrite Z_N_nat. pose proof len_rs. pose proof lenx. destruct Hr as [L0 HH].
  destruct (HH (Z.to_nat (to_Z a)) ltac:(lia)) as (m & E & R).
  rewrite (nth_error_nth _ _ _ E). rewrite Z2Nat.id in R by (pose proof (to_Z_bounded a); lia).
  rewrite of_to_Z in R. unfold repr, repr_uint in R. rewrite <- R.
  rewrite Z2N.id; [reflexivity | apply (proj1 (to_Z_bounded _))].
Qed.

Lemma XX_b : forall i, (i < nN)%N -> (-1000 <= XX i <= 1000)%Z.
Proof.
  intros i Hi. pose proof (vi_xs _ _ _ Hv) as H. rewrite Forall_forall in H. apply H.
  unfold XX. apply nth_In. unfold len in Hi. lia.
Qed.

Lemma YY_b : forall i, (i < nN)%N -> (-1000 <= YY i <= 1000)%Z.
Proof.
  intros i Hi. pose proof (vi_ys _ _ _ Hv) as H. rewrite Forall_forall in H. apply H.
  unfold YY. apply nth_In. pose proof len_ys. unfold len in Hi. lia.
Qed.

Lemma RR_b : forall i, (i < nN)%N -> (1 <= RR i <= 100)%N.
Proof.
  intros i Hi. pose proof (vi_rs _ _ _ Hv) as H. rewrite Forall_forall in H. apply H.
  unfold RR. apply nth_In. pose proof len_rs. unfold len in Hi. lia.
Qed.

Lemma D2_b : forall i j, (i < nN)%N -> (j < nN)%N -> (0 <= D2 i j <= 8000000)%Z.
Proof.
  intros i j Hi Hj. pose proof (XX_b i Hi). pose proof (XX_b j Hj).
  pose proof (YY_b i Hi). pose proof (YY_b j Hj). unfold D2.
  assert (Sq : forall d, (-2000 <= d <= 2000)%Z -> (0 <= d * d <= 4000000)%Z) by (intros; nia).
  pose proof (Sq (XX i - XX j)%Z ltac:(lia)). pose proof (Sq (YY i - YY j)%Z ltac:(lia)). lia.
Qed.

Lemma dsq_spec : forall a b, (to_Z a < to_Z nI)%Z -> (to_Z b < to_Z nI)%Z ->
  to_Z (dsq x y a b) = D2 (toN a) (toN b).
Proof.
  intros a b Ha Hb. unfold dsq. cbv zeta.
  rewrite Uint63.add_spec, !Uint63.mul_spec, !Uint63.sub_spec.
  rewrite <- (Sint63.to_Z_mod_Uint63to_Z x.[a]), <- (Sint63.to_Z_mod_Uint63to_Z x.[b]).
  rewrite <- (Sint63.to_Z_mod_Uint63to_Z y.[a]), <- (Sint63.to_Z_mod_Uint63to_Z y.[b]).
  rewrite (XX_get a Ha), (XX_get b Hb), (YY_get a Ha), (YY_get b Hb).
  repeat rewrite ?Zplus_mod_idemp_l, ?Zplus_mod_idemp_r, ?Zmult_mod_idemp_l, ?Zmult_mod_idemp_r,
    ?Zminus_mod_idemp_l, ?Zminus_mod_idemp_r.
  rewrite Zplus_mod, <- !Zmult_mod, <- Zplus_mod.
  apply Z.mod_small. pose proof (D2_b _ _ (toN_lt a Ha) (toN_lt b Hb)). unfold D2 in *.
  change wB with (2 ^ 63)%Z. lia.
Qed.

Lemma sq_b : forall i j, (i < nN)%N -> (j < nN)%N -> 0 <= sqrt (IZR (D2 i j)) <= 3000.
Proof.
  intros i j Hi Hj. pose proof (D2_b i j Hi Hj). split; [apply sqrt_pos |].
  apply sqrt_le_bound; [lra |]. replace (3000 * 3000) with (IZR 9000000) by (simpl; lra).
  apply IZR_le. lia.
Qed.

Lemma Rs_b : forall i j, (i < nN)%N -> (j < nN)%N -> 2 <= IZR (Z.of_N (RR i + RR j)) <= 200.
Proof.
  intros i j Hi Hj. pose proof (RR_b i Hi). pose proof (RR_b j Hj).
  split; [replace 2 with (IZR 2) by reflexivity | replace 200 with (IZR 200) by reflexivity];
    apply IZR_le; lia.
Qed.

Lemma repr_wt : forall a b, (to_Z a < to_Z nI)%Z -> (to_Z b < to_Z nI)%Z ->
  repr (wt x y r a b) (Wh (toN a) (toN b)).
Proof.
  intros a b Ha Hb. unfold wt, Wh.
  pose proof (toN_lt a Ha) as Ia. pose proof (toN_lt b Hb) as Ib.
  pose proof (D2_b _ _ Ia Ib). pose proof (RR_b _ Ia). pose proof (RR_b _ Ib).
  assert (R1 : repr (of_uint63 (dsq x y a b)) (IZR (D2 (toN a) (toN b)))).
  { rewrite <- dsq_spec by assumption. apply repr_of_uint63_exact. rewrite dsq_spec by assumption. lia. }
  assert (R2 : repr (of_uint63 (r.[a] + r.[b])%uint63) (IZR (Z.of_N (RR (toN a) + RR (toN b))))).
  { assert (E : to_Z (r.[a] + r.[b])%uint63 = Z.of_N (RR (toN a) + RR (toN b))).
    { rewrite Uint63.add_spec, (RR_get a Ha), (RR_get b Hb), <- N2Z.inj_add. apply Z.mod_small. change wB with (2 ^ 63)%Z. lia. }
    rewrite <- E. apply repr_of_uint63_exact. rewrite E. lia. }
  pose proof (repr_sqrt _ _ R1 ltac:(apply IZR_le; lia)) as R3.
  apply repr_sub; [exact R3 | exact R2 |]. apply no_ovf.
  pose proof (sq_b _ _ Ia Ib). pose proof (Rs_b _ _ Ia Ib).
  pose proof (rnd_err (sqrt (IZR (D2 (toN a) (toN b))))) as E.
  rewrite (Rabs_right (sqrt _)) in E by lra. rewrite u_val in E.
  apply Raux.Rabs_le_inv in E. apply Rabs_le. split; lra.
Qed.

Lemma w_eq : forall i j, w xs ys rs i j = sqrt (IZR (D2 i j)) - IZR (Z.of_N (RR i + RR j)).
Proof.
  intros i j. rewrite w_def. unfold dist.
  replace (sqdist (centre xs ys i) (centre xs ys j)) with (IZR (D2 i j)).
  - rewrite N2Z.inj_add, plus_IZR. unfold radius, RR. ring.
  - rewrite sqdist_eq. unfold centre. cbn [fst snd]. unfold D2, XX, YY.
    rewrite plus_IZR, !mult_IZR, !minus_IZR. reflexivity.
Qed.

Lemma u_small : 0 < u <= / 1000000000000.
Proof. pose proof u_pos. rewrite u_val in *. lra. Qed.

Lemma Wh_err : forall i j, (i < nN)%N -> (j < nN)%N -> Rabs (Wh i j - w xs ys rs i j) <= 4000 * u.
Proof.
  intros i j Hi Hj. rewrite w_eq. unfold Wh.
  pose proof (sq_b i j Hi Hj) as Bs. pose proof (Rs_b i j Hi Hj) as Br.
  set (sq := sqrt (IZR (D2 i j))) in *. set (Rs := IZR (Z.of_N (RR i + RR j))) in *.
  pose proof (rnd_err sq) as E1. rewrite (Rabs_right sq) in E1 by lra.
  pose proof u_small as U.
  assert (Su : sq * (u / 2) <= 3000 * (u / 2)) by (apply Rmult_le_compat_r; lra).
  assert (Bb : Rabs (rnd sq - Rs) <= 3201).
  { apply Raux.Rabs_le_inv in E1. apply Rabs_le. split; lra. }
  pose proof (rnd_err (rnd sq - Rs)) as E2.
  replace (rnd (rnd sq - Rs) - (sq - Rs)) with ((rnd (rnd sq - Rs) - (rnd sq - Rs)) + (rnd sq - sq)) by ring.
  eapply Rle_trans; [apply Rabs_triang |].
  assert (Rabs (rnd sq - Rs) * (u / 2) <= 3201 * (u / 2)) by (apply Rmult_le_compat_r; lra).
  lra.
Qed.

Lemma Wh_sym : forall i j, Wh i j = Wh j i.
Proof.
  intros i j. unfold Wh. replace (D2 i j) with (D2 j i) by (unfold D2; ring).
  rewrite N.add_comm. reflexivity.
Qed.

Lemma Wh_nonneg : forall i j, (i < nN)%N -> (j < nN)%N -> i <> j -> 0 <= Wh i j.
Proof.
  intros i j Hi Hj Hij. pose proof (w_nonneg xs ys rs Hv i j Hi Hj Hij) as H. rewrite w_eq in H.
  unfold Wh. pose proof (RR_b i Hi). pose proof (RR_b j Hj).
  assert (E : rnd (IZR (Z.of_N (RR i + RR j))) = IZR (Z.of_N (RR i + RR j))) by (apply rnd_IZR; lia).
  rewrite <- rnd_0. apply rnd_le.
  assert (L2 : IZR (Z.of_N (RR i + RR j)) <= rnd (sqrt (IZR (D2 i j)))).
  { rewrite <- E. apply rnd_le. lra. }
  lra.
Qed.

Lemma Wh_le : forall i j, (i < nN)%N -> (j < nN)%N -> Wh i j <= 3001.
Proof.
  intros i j Hi Hj. pose proof (Wh_err i j Hi Hj) as E. rewrite w_eq in E.
  pose proof (sq_b i j Hi Hj). pose proof (Rs_b i j Hi Hj). pose proof u_small.
  apply Raux.Rabs_le_inv in E. lra.
Qed.

Lemma cost_Wh_b : forall E, Forall (okedge nN) E -> 0 <= costE Wh E <= 3001 * INR (List.length E).
Proof.
  intros E H; induction H as [| e E (H1 & H2 & H3) _ IH]; simpl; [lra |].
  pose proof (Wh_nonneg _ _ H1 H2 H3). pose proof (Wh_le _ _ H1 H2).
  destruct (List.length E); simpl in *; lra.
Qed.

Definition inv_state (S : list N) (inT : array bool) (key : array float) : Prop :=
  PArray.length inT = nI /\ PArray.length key = nI /\
  (forall v, (to_Z v < to_Z nI)%Z -> (inT.[v] = true <-> In (toN v) S)) /\
  (forall v, (to_Z v < to_Z nI)%Z -> inT.[v] = false ->
     repr key.[v] (fval key.[v]) /\ (exists s, In s S /\ fval key.[v] = Wh s (toN v)) /\
     (forall s, In s S -> fval key.[v] <= Wh s (toN v))).

Lemma lt0 : forall v : int, (to_Z v < to_Z 0%uint63)%Z -> False.
Proof. intros v H. pose proof (to_Z_bounded v). change (to_Z 0%uint63) with 0%Z in H. lia. Qed.

Lemma n_pos : (to_Z 0%uint63 <= to_Z nI)%Z.
Proof. pose proof (to_Z_bounded nI). change (to_Z 0%uint63) with 0%Z. lia. Qed.

Lemma amin_spec : forall S inT key, inv_state S inT key ->
  (exists v, (to_Z v < to_Z nI)%Z /\ inT.[v] = false) ->
  forall b bv, loop nI (amin_step nI inT key) 0%uint63 (nI, PrimFloat.zero) = (b, bv) ->
  (to_Z b < to_Z nI)%Z /\ inT.[b] = false /\
  forall v, (to_Z v < to_Z nI)%Z -> inT.[v] = false -> fval key.[b] <= fval key.[v].
Proof.
  intros S inT key (Li & Lk & Hin & Hk) (v0 & Hv0 & Fv0) b bv E.
  set (Q := fun (j : int) (st : int * float) =>
    (fst st = nI /\ forall v, (to_Z v < to_Z j)%Z -> inT.[v] = true) \/
    ((to_Z (fst st) < to_Z j)%Z /\ inT.[fst st] = false /\ snd st = key.[fst st] /\
     forall v, (to_Z v < to_Z j)%Z -> inT.[v] = false -> fval key.[fst st] <= fval key.[v])).
  assert (HQ : Q nI (loop nI (amin_step nI inT key) 0%uint63 (nI, PrimFloat.zero))).
  { apply for_inv; [apply n_pos | left; split; [reflexivity | intros v Hvv; exfalso; exact (lt0 v Hvv)] |].
    intros j [b' bv'] Hj HQj. unfold amin_step.
    assert (Hjn : (to_Z j < to_Z nI)%Z) by lia.
    pose proof (succ_spec j nI Hjn) as Sj.
    destruct (inT.[j]) eqn:Tj.
    - destruct HQj as [[Eb Hall] | (Hb & Fb & Eb & Hm)]; [left | right]; cbn [fst snd] in *.
      + split; [exact Eb |]. intros v Hvv. destruct (lt_succ j nI v Hjn Hvv) as [H | ->]; auto.
      + split; [lia |]. split; [exact Fb |]. split; [exact Eb |].
        intros v Hvv Fv. destruct (lt_succ j nI v Hjn Hvv) as [H | ->]; [auto | congruence].
    - destruct (b' =? nI)%uint63 eqn:Eb.
      + apply Uint63.eqb_spec in Eb. subst b'.
        right. cbn [fst snd]. split; [lia |]. split; [exact Tj |]. split; [reflexivity |].
        intros v Hvv Fv. destruct (lt_succ j nI v Hjn Hvv) as [H | ->]; [| lra].
        destruct HQj as [[_ Hall] | (Hb & _)]; cbn [fst] in *.
        * rewrite Hall in Fv by exact H. discriminate.
        * lia.
      + assert (Nb : b' <> nI) by (intros ->; rewrite Uint63.eqb_refl in Eb; discriminate).
        destruct HQj as [[Eb' _] | (Hb & Fb & Ebv & Hm)]; cbn [fst snd] in *; [congruence |].
        pose proof (Hk j Hjn Tj) as (Rj & _). pose proof (Hk b' ltac:(lia) Fb) as (Rb & _).
        rewrite Ebv. destruct (key.[j] <? key.[b'])%float eqn:C.
        * apply (repr_ltb_iff _ _ _ _ Rj Rb) in C.
          right. cbn [fst snd]. split; [lia |]. split; [exact Tj |]. split; [reflexivity |].
          intros v Hvv Fv. destruct (lt_succ j nI v Hjn Hvv) as [H | ->]; [| lra].
          pose proof (Hm v H Fv). lra.
        * assert (C' : ~ fval key.[j] < fval key.[b']).
          { rewrite <- (repr_ltb_iff _ _ _ _ Rj Rb). congruence. }
          right. cbn [fst snd]. split; [lia |]. split; [exact Fb |]. split; [reflexivity |].
          intros v Hvv Fv. destruct (lt_succ j nI v Hjn Hvv) as [H | ->]; [auto | lra]. }
  rewrite E in HQ. destruct HQ as [[_ Hall] | (Hb & Fb & _ & Hm)]; cbn [fst snd] in *.
  - rewrite Hall in Fv0 by exact Hv0. discriminate.
  - auto.
Qed.

Lemma upd_spec : forall S inT key b, inv_state S inT key -> (to_Z b < to_Z nI)%Z -> inT.[b] = false ->
  inv_state (toN b :: S) inT.[b <- true] (loop nI (upd_step x y r inT.[b <- true] b) 0%uint63 key).
Proof.
  intros S inT key b (Li & Lk & Hin & Hk) Hb Fb.
  set (inT' := inT.[b <- true]).
  assert (T' : forall v, v <> b -> inT'.[v] = inT.[v]) by (intros v Hvb; apply bget_set_other; auto).
  assert (Tb : inT'.[b] = true).
  { apply bget_set_same. rewrite Li. apply Uint63.ltb_spec. exact Hb. }
  set (U := fun (j : int) (k' : array float) => PArray.length k' = nI /\
    forall v, (to_Z v < to_Z nI)%Z -> inT'.[v] = false ->
      ((to_Z v < to_Z j)%Z -> repr k'.[v] (fval k'.[v]) /\ fval k'.[v] <= fval key.[v] /\
         fval k'.[v] <= Wh (toN b) (toN v) /\
         (fval k'.[v] = fval key.[v] \/ fval k'.[v] = Wh (toN b) (toN v))) /\
      ((to_Z j <= to_Z v)%Z -> k'.[v] = key.[v])).
  assert (HU : U nI (loop nI (upd_step x y r inT' b) 0%uint63 key)).
  { apply for_inv; [apply n_pos | split; [exact Lk |] |].
    - intros v Hvv Fv. split; [intros H; exfalso; exact (lt0 v H) | reflexivity].
    - intros j k' Hj (Lk' & Hu). assert (Hjn : (to_Z j < to_Z nI)%Z) by lia.
      pose proof (succ_spec j nI Hjn) as Sj. unfold upd_step.
      destruct (inT'.[j]) eqn:Tj.
      + split; [exact Lk' |]. intros v Hvv Fv. destruct (Hu v Hvv Fv) as [H1 H2]. split.
        * intros Hvj. destruct (lt_succ j nI v Hjn Hvj) as [H | ->]; [auto | congruence].
        * intros Hvj. apply H2. lia.
      + assert (Njb : j <> b) by (intros ->; congruence).
        assert (Fj : inT.[j] = false) by (rewrite <- (T' j Njb); exact Tj).
        destruct (Hk j Hjn Fj) as (Rkj & _).
        assert (Ekj : k'.[j] = key.[j]) by (apply (proj2 (Hu j Hjn Tj)); lia).
        pose proof (repr_wt b j Hb Hjn) as Rw.
        rewrite Ekj. destruct (wt x y r b j <? key.[j])%float eqn:C.
        * apply (repr_ltb_iff _ _ _ _ Rw Rkj) in C.
          split; [rewrite flength_set; exact Lk' |].
          intros v Hvv Fv. destruct (Uint63.eqs v j) as [-> | Nvj].
          -- rewrite fget_set_same by (rewrite Lk'; apply Uint63.ltb_spec; exact Hjn).
             destruct Rw as [Rw1 Rw2]. rewrite Rw2.
             split; [intros _ | intros H; lia].
             split; [split; [exact Rw1 | exact Rw2] |]. split; [lra |]. split; [lra | right; reflexivity].
          -- rewrite fget_set_other by (intros E; apply Nvj; symmetry; exact E).
             destruct (Hu v Hvv Fv) as [H1 H2]. split.
             ++ intros Hvj. destruct (lt_succ j nI v Hjn Hvj) as [H | ->]; [auto | congruence].
             ++ intros Hvj. apply H2. lia.
        * assert (C' : ~ Wh (toN b) (toN j) < fval key.[j]).
          { rewrite <- (repr_ltb_iff _ _ _ _ Rw Rkj). congruence. }
          split; [exact Lk' |]. intros v Hvv Fv. destruct (Uint63.eqs v j) as [-> | Nvj].
          -- split; [intros _ | intros H; lia].
             rewrite Ekj. split; [exact Rkj |]. split; [lra |]. split; [lra | left; reflexivity].
          -- destruct (Hu v Hvv Fv) as [H1 H2]. split.
             ++ intros Hvj. destruct (lt_succ j nI v Hjn Hvj) as [H | ->]; [auto | congruence].
             ++ intros Hvj. apply H2. lia. }
  destruct HU as (Lk'' & Hu). split; [unfold inT'; rewrite blength_set; exact Li |].
  split; [exact Lk'' |]. split.
  - intros v Hvv. destruct (Uint63.eqs v b) as [-> | Nvb].
    + rewrite Tb. split; [intros _; left; reflexivity | reflexivity].
    + rewrite (T' v Nvb), (Hin v Hvv). split; [intros H; right; exact H |].
      intros [E | H]; [exfalso; apply Nvb; apply toN_inj; symmetry; exact E | exact H].
  - intros v Hvv Fv. assert (Nvb : v <> b) by (intros ->; congruence).
    assert (Fv0 : inT.[v] = false) by (rewrite <- (T' v Nvb); exact Fv).
    destruct (Hk v Hvv Fv0) as (_ & (s0 & Hs0 & Es0) & Hle).
    destruct (proj1 (Hu v Hvv Fv) Hvv) as (Rv & L1 & L2 & [E | E]).
    + split; [exact Rv |]. split; [exists s0; split; [right; exact Hs0 | rewrite E; exact Es0] |].
      intros s [<- | Hs]; [exact L2 |]. pose proof (Hle s Hs). lra.
    + split; [exact Rv |]. split; [exists (toN b); split; [left; reflexivity | exact E] |].
      intros s [<- | Hs]; [exact L2 |]. pose proof (Hle s Hs). lra.
Qed.

Definition Pinv (k : int) (st : array bool * array float * float) : Prop :=
  let '(inT, key, tot) := st in
  exists S steps, run Wh nN [0%N] steps S /\ NoDup S /\ Z.of_nat (List.length S) = to_Z k /\
    (forall s, In s S -> (s < nN)%N) /\ inv_state S inT key /\ repr tot (fval tot) /\
    Rabs (fval tot - costE Wh steps) <= INR (List.length steps) * u * (costE Wh steps + 1).

Lemma all_in : forall S, NoDup S -> (forall s, In s S -> (s < nN)%N) ->
  (N.to_nat nN <= List.length S)%nat -> forall t, (t < nN)%N -> In t S.
Proof.
  intros S ND HS L t Ht.
  refine (@NoDup_length_incl N S (verts nN) ND _ _ t _).
  - rewrite verts_length. exact L.
  - intros s Hs. apply verts_In. auto.
  - apply verts_In. exact Ht.
Qed.

Lemma step_spec : forall k st, (1 <= to_Z k < to_Z nI)%Z -> Pinv k st ->
  Pinv (k + 1)%uint63 (prim_step x y r nI k st).
Proof.
  intros k [[inT key] tot] Hk (S & steps & R & ND & LS & HS & Inv & Rt & Et).
  pose proof Inv as (Li & Lk & Hin & Hkey).
  unfold prim_step.
  destruct (loop nI (amin_step nI inT key) 0%uint63 (nI, PrimFloat.zero)) as [b bv] eqn:EL.
  assert (Ex : exists v, (to_Z v < to_Z nI)%Z /\ inT.[v] = false).
  { destruct (classic (exists v, (to_Z v < to_Z nI)%Z /\ inT.[v] = false)) as [H | H]; [exact H | exfalso].
    assert (All : forall t, (t < nN)%N -> In t S).
    { intros t Ht. destruct (ofN_spec t Ht) as [E1 E2].
      assert (Hot : (to_Z (ofN t) < to_Z nI)%Z) by (rewrite E1, nI_eq; lia).
      destruct (inT.[ofN t]) eqn:T.
      - apply (Hin _ Hot) in T. rewrite E2 in T. exact T.
      - exfalso. apply H. exists (ofN t). auto. }
    pose proof (NoDup_incl_length (verts_NoDup nN) (fun t Ht => All t (proj1 (verts_In nN t) Ht))) as L.
    rewrite verts_length in L. pose proof nI_eq. lia. }
  destruct (amin_spec S inT key Inv Ex b bv EL) as (Hb & Fb & Hmin).
  destruct (Hkey b Hb Fb) as (Rb & (p & Hp & Ep) & _).
  set (tb := toN b) in *.
  assert (Hbn : (tb < nN)%N) by (apply toN_lt; exact Hb).
  assert (HbS : ~ In tb S) by (intros H; apply (Hin b Hb) in H; congruence).
  assert (Hpn : (p < nN)%N) by auto.
  assert (Npb : p <> tb) by (intros ->; contradiction).
  assert (Hmp : minp Wh nN S p tb).
  { intros s t Hs Ht HtS. destruct (ofN_spec t Ht) as [E1 E2].
    assert (Hot : (to_Z (ofN t) < to_Z nI)%Z) by (rewrite E1, nI_eq; lia).
    assert (Ft : inT.[ofN t] = false).
    { destruct (inT.[ofN t]) eqn:T; [| reflexivity]. apply (Hin _ Hot) in T. rewrite E2 in T. contradiction. }
    destruct (Hkey (ofN t) Hot Ft) as (_ & _ & Hle).
    rewrite <- Ep. specialize (Hle s Hs). rewrite E2 in Hle. pose proof (Hmin (ofN t) Hot Ft). lra. }
  pose proof (run_snoc Wh nN [0%N] steps S p tb R Hp Hbn HbS Hmp) as R'.
  destruct (run_nodup Wh nN _ _ _ R ltac:(constructor; [intros [] | constructor])) as [_ LS'].
  destruct (run_ok Wh nN _ _ _ R ltac:(intros s [<- | []]; pose proof nI_eq; pose proof n_bounds; lia)) as [Ok _].
  pose proof (cost_Wh_b steps Ok) as Cb.
  pose proof (Wh_nonneg p tb Hpn Hbn Npb) as Wp0. pose proof (Wh_le p tb Hpn Hbn) as Wp1.
  assert (Kb : 0 <= INR (List.length steps) <= 2000).
  { split; [apply pos_INR |]. replace 2000 with (INR 2000) by (simpl; lra). apply le_INR.
    simpl in LS'. pose proof n_bounds. lia. }
  set (cc := costE Wh steps) in *.
  set (a := fval key.[b]) in *.
  pose proof u_small as U.
  assert (Vt : Rabs (fval tot) <= 7000000).
  { assert (INR (List.length steps) * u * (cc + 1) <= 1).
    { assert (H1 : INR (List.length steps) * u <= 2000 * / 1000000000000).
      { apply Rmult_le_compat; lra. }
      assert (H2 : cc + 1 <= 6003001) by nra.
      assert (H3 : INR (List.length steps) * u * (cc + 1) <= (2000 * / 1000000000000) * 6003001).
      { apply Rmult_le_compat; try lra. apply Rmult_le_pos; lra. }
      lra. }
    assert (cc <= 6002000) by nra.
    apply Raux.Rabs_le_inv in Et. apply Rabs_le. lra. }
  assert (Rt' : repr (tot + key.[b])%float (rnd (fval tot + a))).
  { apply repr_add; [exact Rt | exact Rb |]. apply no_ovf.
    eapply Rle_trans; [apply Rabs_triang |]. rewrite (Rabs_right a) by lra. lra. }
  exists (tb :: S), (steps ++ [(p, tb)]). split; [exact R' |]. split; [constructor; auto |].
  split; [simpl List.length; rewrite (succ_spec k nI ltac:(lia)); lia |].
  split; [intros s [<- | Hs]; auto |].
  split; [apply upd_spec; auto |].
  pose proof Rt' as [_ Ft']. split; [rewrite Ft'; exact Rt' |].
  rewrite Ft'. rewrite costE_app. simpl costE. rewrite Rplus_0_r. fold cc.
  rewrite length_app, plus_INR. simpl (INR (List.length [(p, tb)])).
  rewrite <- Ep. fold a.
  replace (cc + a + 1) with (cc + a + 1) by reflexivity.
  apply acc_err; auto; lra.
Qed.

Lemma init_spec : Pinv 1%uint63
  ((PArray.make nI false).[0%uint63 <- true],
   loop nI (init_step x y r) 0%uint63 (PArray.make nI PrimFloat.zero), PrimFloat.zero).
Proof.
  pose proof n_bounds as Nb. pose proof nI_eq as NE.
  assert (Lmax : (nI <=? max_length)%uint63 = true).
  { apply Uint63.leb_spec. change (to_Z max_length) with 4194303%Z. lia. }
  set (key0 := loop nI (init_step x y r) 0%uint63 (PArray.make nI PrimFloat.zero)).
  assert (HK : PArray.length key0 = nI /\
     forall v, (to_Z v < to_Z nI)%Z -> key0.[v] = wt x y r 0%uint63 v).
  { set (I := fun (j : int) (k : array float) => PArray.length k = nI /\
        forall v, (to_Z v < to_Z j)%Z -> k.[v] = wt x y r 0%uint63 v).
    assert (I nI key0); [| destruct H as [H1 H2]; split; [exact H1 | exact H2]].
    apply for_inv; [apply n_pos | split |].
    - rewrite flength_make, Lmax. reflexivity.
    - intros v Hvv. exfalso. exact (lt0 v Hvv).
    - intros j k Hj (L & Hk). assert (Hjn : (to_Z j < to_Z nI)%Z) by lia. unfold init_step.
      split; [rewrite flength_set; exact L |]. intros v Hvv.
      destruct (Uint63.eqs v j) as [-> | Nvj].
      + apply fget_set_same. rewrite L. apply Uint63.ltb_spec. exact Hjn.
      + rewrite fget_set_other by (intros E; apply Nvj; symmetry; exact E).
        destruct (lt_succ j nI v Hjn Hvv) as [H | ->]; [auto | congruence]. }
  destruct HK as [Lk0 Hk0].
  assert (T0 : forall v, ((PArray.make nI false).[0%uint63 <- true]).[v] = true <-> v = 0%uint63).
  { intros v. destruct (Uint63.eqs v 0%uint63) as [-> | Nv].
    - rewrite bget_set_same; [tauto |]. rewrite blength_make, Lmax.
      apply Uint63.ltb_spec. change (to_Z 0%uint63) with 0%Z. lia.
    - rewrite bget_set_other by (intros E; apply Nv; symmetry; exact E).
      rewrite bget_make. split; [discriminate | intros E; contradiction]. }
  assert (Z0 : toN 0%uint63 = 0%N) by reflexivity.
  exists [0%N], []. split; [constructor |]. split; [constructor; [intros [] | constructor] |].
  split; [reflexivity |]. split; [intros s [<- | []]; lia |].
  split.
  - split; [rewrite blength_set, blength_make, Lmax; reflexivity |]. split; [exact Lk0 |].
    split.
    + intros v Hvv. rewrite T0. split.
      * intros ->. left. reflexivity.
      * intros [E | []]. apply toN_inj. rewrite <- E. reflexivity.
    + intros v Hvv Fv. assert (Nv : v <> 0%uint63) by (intros E; apply T0 in E; congruence).
      pose proof (repr_wt 0%uint63 v ltac:(change (to_Z 0%uint63) with 0%Z; lia) Hvv) as Rw.
      rewrite Hk0 by exact Hvv. pose proof Rw as [_ Ew]. rewrite Z0 in Rw, Ew. rewrite Ew.
      split; [exact Rw |].
      split; [exists 0%N; split; [left; reflexivity | reflexivity] |].
      intros s [<- | []]. lra.
  - split; [exact repr_zero |]. simpl. rewrite (proj2 repr_zero).
    rewrite Rminus_0_r, Rabs_R0. lra.
Qed.

Lemma comsat_main : exists v, repr (comsat x y r) v /\ communicationssatellite_spec xs ys rs v.
Proof.
  pose proof n_bounds as Nb. pose proof nI_eq as NE.
  unfold comsat.
  assert (HP : Pinv nI (loop nI (prim_step x y r nI) 1%uint63
     ((PArray.make nI false).[0%uint63 <- true],
      loop nI (init_step x y r) 0%uint63 (PArray.make nI PrimFloat.zero), PrimFloat.zero))).
  { apply for_inv; [change (to_Z 1%uint63) with 1%Z; lia | exact init_spec |].
    intros j st Hj P. apply step_spec; [change (to_Z 1%uint63) with 1%Z in Hj; lia | exact P]. }
  destruct (loop nI (prim_step x y r nI) 1%uint63 _) as [[inT key] tot].
  destruct HP as (S & steps & R & ND & LS & HS & _ & Rt & Et).
  exists (fval tot). split; [exact Rt |].
  destruct (exact_min xs ys rs Hv) as (st2 & S2 & R2 & All2 & Hmin).
  exists (costE (w xs ys rs) st2). split; [exact Hmin |].
  assert (All : forall t, (t < nN)%N -> In t S) by (apply all_in; auto; lia).
  assert (R0 : forall s, In s [0%N] -> (s < nN)%N) by (intros s [<- | []]; lia).
  destruct (run_ok _ _ _ _ _ R R0) as [Ok _].
  destruct (run_ok _ _ _ _ _ R2 R0) as [Ok2 HS2].
  destruct (run_nodup _ _ _ _ _ R ltac:(constructor; [intros [] | constructor])) as [_ L1].
  destruct (run_nodup _ _ _ _ _ R2 ltac:(constructor; [intros [] | constructor])) as [ND2 L2].
  assert (L2' : (List.length S2 <= N.to_nat nN)%nat).
  { rewrite <- (verts_length nN). apply NoDup_incl_length; [exact ND2 |].
    intros s Hs. apply verts_In. auto. }
  simpl in L1, L2.
  assert (K1 : INR (List.length steps) <= 2000).
  { replace 2000 with (INR 2000) by (simpl; lra). apply le_INR. lia. }
  assert (K2 : INR (List.length st2) <= 2000).
  { replace 2000 with (INR 2000) by (simpl; lra). apply le_INR. lia. }
  assert (Conn : forall (st : list (N * N)) S', run Wh nN [0%N] st S' \/ run (w xs ys rs) nN [0%N] st S' ->
     (forall t, (t < nN)%N -> In t S') ->
     forall t, (t < nN)%N -> exists s, In s [0%N] /\ clos_refl_trans N (edge st) t s).
  { intros st S' [Rr | Rr] Al t Ht; eapply run_conn; eauto. }
  (* m <= cost_w (Prim's tree on Wh) and cost_Wh <= cost_Wh (exact tree) *)
  pose proof (prim_lower (w xs ys rs) nN (w_sym xs ys rs) (w_nonneg xs ys rs Hv) _ _ _ R2 steps Ok
     (Conn steps S (or_introl R) All)) as P1.
  pose proof (prim_lower Wh nN Wh_sym Wh_nonneg _ _ _ R st2 Ok2 (Conn st2 S2 (or_intror R2) All2)) as P2.
  assert (D : forall E, Forall (okedge nN) E ->
     Rabs (costE Wh E - costE (w xs ys rs) E) <= INR (List.length E) * (4000 * u)).
  { intros E HE. apply costE_diff. intros e He. rewrite Forall_forall in HE.
    destruct (HE e He) as (H1 & H2 & _). apply Wh_err; auto. }
  pose proof (D steps Ok) as D1. pose proof (D st2 Ok2) as D2.
  pose proof u_small as U.
  set (m := costE (w xs ys rs) st2) in *. set (cc := costE Wh steps) in *.
  pose proof (cost_Wh_b steps Ok) as Cb. fold cc in Cb.
  assert (M0 : 0 <= m) by (apply (costE_nonneg (w xs ys rs) nN (w_nonneg xs ys rs Hv)); exact Ok2).
  apply Raux.Rabs_le_inv in D1. apply Raux.Rabs_le_inv in D2.
  assert (E1 : INR (List.length steps) * (4000 * u) <= 2000 * (4000 * u)) by (apply Rmult_le_compat_r; lra).
  assert (E2 : INR (List.length st2) * (4000 * u) <= 2000 * (4000 * u)) by (apply Rmult_le_compat_r; lra).
  assert (E3 : INR (List.length steps) * u * (cc + 1) <= 2000 * u * (cc + 1)).
  { apply Rmult_le_compat_r; [lra |]. apply Rmult_le_compat_r; lra. }
  assert (Ccm : Rabs (cc - m) <= 8000000 * u) by (apply Rabs_le; split; lra).
  assert (Tot : Rabs (fval tot - m) <= 2000 * u * (cc + 1) + 8000000 * u).
  { replace (fval tot - m) with ((fval tot - cc) + (cc - m)) by ring.
    eapply Rle_trans; [apply Rabs_triang | lra]. }
  rewrite u_val in *. unfold within_tolerance.
  apply Raux.Rabs_le_inv in Ccm.
  destruct (Rle_or_lt m 1) as [Hm | Hm].
  - left. lra.
  - right. rewrite (Rabs_right m) by lra. lra.
Qed.

End Mach.

Definition communicationssatellite : array sint -> array sint -> array uint -> float := comsat.

Lemma communicationssatellite_correct :
  forall (xs ys : list Z) (rs : list N) (x y : array sint) (r : array uint),
    valid_input xs ys rs -> repr x xs -> repr y ys -> repr r rs ->
    exists v : R, repr (communicationssatellite x y r) v /\
      communicationssatellite_spec xs ys rs v.
Proof. intros xs ys rs x y r Hv Hx Hy Hr. exact (comsat_main xs ys rs x y r Hv Hx Hy Hr). Qed.
