(* Correctness proofs for roadtimes_implem.v. *)
(* Implementation of roadtimes.spec: Floyd-Warshall with a successor
   table, then the two-phase simplex method (lexicographic pivoting rule) on
   an exact rational tableau, two solves per query.

   Code.
   - P_RP: the n x n matrix is flattened (fill2); Floyd-Warshall on two flat
     n*n tables, distances D (no road: INF = 2^30) and successors X, the k
     loop outermost, in place (fw_cell).  scan_roads numbers the roads
     (positive entries) in row-major order: I.[i*n+j] is the index of road
     (i, j), P.[e] its position.  walk follows the successors from s to d
     (erased Acc on D.[cur*n+d], which strictly decreases along the walk) and
     counts the roads used in a flat array cnt of length E.
   - The LP (bound_rows, deliv_row, build_T): one variable per road,
     x_e = (minutes on road e) - (its length) in [0, length_e]; columns
     x_e (e < E), the slack y_e of x_e <= length_e (E + e), the artificial
     variable of delivery k (2E + k); rows x_e + y_e = length_e and, for
     delivery k, sum_e cnt_k(e) x_e + a_k = t_k - D_k (row negated but a_k
     when the right-hand side is negative).  One flat array of rationals
     (QArith Q, kept reduced by zgcd), m = E + R rows of w = 2E + R + 1
     cells, the last column being the right-hand side.
   - P_SP: the simplex.  enter: first allowed column of negative reduced
     cost; leave: lexicographic minimum ratio, the lexicographic vector of a
     row being its right-hand side followed by its entries in the columns of
     the initial basis (E .. N-1); pivot: in place, row by row.  sloop
     recurses on an erased Acc of the pivot relation.  P_SV: phase 1
     minimises the sum of the artificial variables once; phase 2 runs, for
     each query, from a copy of the phase-1 tableau, with the columns of
     zero phase-1 reduced cost before the artificial ones allowed, on the
     cost vector of the query route (min) and on its opposite (max).
   - The answer of a query is D_q + min and D_q - min(-cost), each turned
     into a float by q2f: floor(q * 2^36) as an int, divided by 2^36.
   - Every loop is the forl / loop combinator (erased Acc (Zwf 0) on
     hi - i), or an erased Acc on a Z measure (walk, zofi, iofz), or the
     erased Acc of sloop.  No nat in the code; Z only inside the LP values
     (rationals) and the conversions zofi / iofz around them.

   Proof.
   - P_SM: the simplex on functions nat -> nat -> R.  The invariant Valid
     (the tableau has the solutions of the initial system, its basis
     columns are unit columns, the reduced costs vanish on the basis and
     express the cost on the solutions, every row is lexicographically
     positive) is kept by a pivot chosen by the rule (pivot_valid), and the
     reduced-cost vector strictly increases (pivot_lex).  Termination
     (acc_fin): the reduced costs are determined by the basis
     (determination, through test vectors), bases are finitely many
     (all_keys), so the lexicographically increasing chain is finite.
     Reading the answer: the basic solution is feasible and attains the
     objective, nothing feasible is below it (opt_lb, phase1_zero,
     phase2_opt); an unbounded column contradicts boundedness (no_ray).
   - P_SP / P_SL / P_SV: the array program computes these functions
     (cellZ_set, scale_row_spec, elim_all_spec, pivot_corr, lexless_spec,
     leave_all, enter_all), acc_VS builds the Acc proof, phase2_min states
     the result: the value is the minimum of the cost over the feasible
     set, attained.
   - P_G, P_FWM, P_FWP, P_FWQ, P_WK: Floyd-Warshall keeps, after k rounds,
     D[a][b] <= D[a][c] + D[c][b] for c < k, D <= road lengths, and
     D[a][b] >= len(a, X[a][b]) + D[X[a][b]][b] (inv_step); hence D is below
     the length of every route (inv_route) and the successor walk builds a
     route of length <= D, i.e. a shortest one, i.e. the unique one.  A
     shortest route has no repeated city (shortest_nodup), so D_q < INF.
   - P_BLD: the tableau built is the formula T0f, unit columns, non-negative
     right-hand sides (build_ok: the hypotheses P1ok of the driver).
   - P_MS3: x in [0, length] satisfying the delivery rows <-> speed limits
     in [30, 60] explaining the deliveries (v = 60 len / (len + x)), and
     the duration of a route is its length plus the x of its roads
     (dur_gen, possible_iff); the LP is bounded and feasible
     (vi_consistent); so D_q + min is the least possible duration and
     D_q - min(-cost) the greatest (query_sem); q2f is within 2^-35
     (q2f_spec, through ReprFloat).
   - P_MF: the answer array, cell by cell. *)
From Speck Require Import Prelude.
From Stdlib Require Import Uint63 PArray ZifyUint63 Arith ZArith NArith List Bool Lia Zwf.
From Stdlib Require Import Reals Lra QArith Qreals PrimFloat ListDec Decidable.
From Stdlib Require Sint63.
From Respeced Require Import Repr ZBig ReprFloat.
From Flocq Require Core.Raux Core.Zaux.

Unset Lia Cache.

Require Export roadtimes_implem.



(* ================================================================== *)
Section P_G.
Import ListNotations.
Open Scope N_scope.

Section G.
Variable dist : list (list Z).

Lemma distance_cons2 : forall a b l, distance dist (a :: b :: l) = (entry dist a b + distance dist (b :: l))%Z.
Proof. reflexivity. Qed.

Lemma route_head : forall s d p, route dist s d p -> exists tl, p = s :: tl.
Proof. intros s d p H. destruct H; eexists; reflexivity. Qed.

Lemma route_cities : forall s d p, route dist s d p -> forall x, In x p -> x < len dist.
Proof.
  intros s d p H. induction H as [s Hs | s m d p Hr Hp IH]; intros x Hx.
  - destruct Hx as [<-|[]]. exact Hs.
  - destruct Hx as [<-|Hx]; [apply Hr | apply IH; exact Hx].
Qed.

Lemma route_ends : forall s d p, route dist s d p -> s < len dist /\ d < len dist.
Proof.
  intros s d p H. induction H as [s Hs | s m d p Hr Hp IH]; [auto|].
  split; [apply Hr | apply IH].
Qed.

Lemma route_join : forall s m p1, route dist s m p1 -> forall d p2, route dist m d p2 ->
  route dist s d (p1 ++ tl p2) /\
  distance dist (p1 ++ tl p2) = (distance dist p1 + distance dist p2)%Z.
Proof.
  intros s m p1 H. induction H as [s Hs | s m' m p Hr Hp IH]; intros d p2 H2.
  - destruct (route_head _ _ _ H2) as [tl E]. subst p2. simpl. split; [exact H2|]. lia.
  - destruct (IH d p2 H2) as [R E]. split.
    + simpl. apply route_step with m'; assumption.
    + destruct (route_head _ _ _ Hp) as [tl Et]. subst p. simpl app.
      rewrite !distance_cons2. simpl app in E. rewrite E. lia.
Qed.

Lemma route_split : forall l1 s d v l2, route dist s d (l1 ++ v :: l2) ->
  route dist s v (l1 ++ [v]) /\ route dist v d (v :: l2) /\
  distance dist (l1 ++ v :: l2) = (distance dist (l1 ++ [v]) + distance dist (v :: l2))%Z.
Proof.
  induction l1 as [|x l1 IH]; intros s d v l2 H.
  - simpl in *. destruct (route_head _ _ _ H) as [tl E]. inversion E. subst.
    split; [apply route_here; apply (route_ends _ _ _ H)|]. split; [exact H|]. simpl. lia.
  - simpl in H. inversion H as [s' Hs' Es | s' m d' p Hr Hp Es Ed Ep]; subst.
    + destruct l1; discriminate.
    + destruct (IH m d v l2 Hp) as (R1 & R2 & E). split; [|split; [exact R2|]].
      * simpl. apply route_step with m; assumption.
      * destruct (route_head _ _ _ Hp) as [tl Et]. simpl app. rewrite Et.
        destruct (route_head _ _ _ R1) as [tl' Et']. rewrite Et'.
        rewrite !distance_cons2. rewrite <- Et, <- Et'. rewrite E. lia.
Qed.

Lemma distance_nonneg : forall s d p, route dist s d p -> (0 <= distance dist p)%Z.
Proof.
  intros s d p H. induction H as [s Hs | s m d p Hr Hp IH]; [simpl; lia|].
  destruct (route_head _ _ _ Hp) as [tl Et]. subst p. rewrite distance_cons2.
  destruct Hr as (_ & _ & Hr). lia.
Qed.

Lemma distance_pos : forall s d x l, route dist s d (s :: x :: l) -> (0 < distance dist (s :: x :: l))%Z.
Proof.
  intros s d x l H. inversion H; subst. rewrite distance_cons2.
  destruct (route_head _ _ _ H4) as [tl Et]. inversion Et; subst.
  pose proof (distance_nonneg _ _ _ H4). destruct H1 as (_ & _ & H1). lia.
Qed.

Lemma shortest_nodup : forall s d p, shortest_route dist s d p -> NoDup p.
Proof.
  intros s d p [Hr Hmin].
  assert (Dec : decidable_eq N) by (intros x y; unfold decidable; destruct (N.eq_dec x y); tauto).
  destruct (NoDup_decidable Dec p) as [ND|ND]; [exact ND|]. exfalso.
  destruct (not_NoDup Dec ND) as (v & l1 & l2 & l3 & ->).
  destruct (route_split l1 s d v (l2 ++ v :: l3) Hr) as (R1 & R2 & E1).
  destruct (route_split (v :: l2) v d v l3 R2) as (R3 & R4 & E2).
  destruct (route_join s v (l1 ++ [v]) R1 d (v :: l3) R4) as [R5 E3].
  simpl tl in R5, E3.
  assert (Ej : (l1 ++ [v]) ++ l3 = l1 ++ v :: l3) by (rewrite <- app_assoc; reflexivity).
  rewrite Ej in R5, E3.
  pose proof (Hmin _ R5) as L.
  assert (P : (0 < distance dist (v :: l2 ++ [v]))%Z).
  { destruct (l2 ++ [v]) as [|x l] eqn:El; [destruct l2; discriminate|].
    apply (distance_pos v v x l). simpl in R3. rewrite El in R3. exact R3. }
  simpl app in E2. rewrite E1, E2 in L. rewrite E3 in L. lia.
Qed.

Lemma nodup_length : forall (p : list N) n, NoDup p -> (forall x, In x p -> x < n) ->
  (List.length p <= N.to_nat n)%nat.
Proof using.
  intros p n ND H.
  rewrite <- (length_seq (N.to_nat n) 0), <- (length_map N.of_nat (seq 0 (N.to_nat n))).
  apply NoDup_incl_length; [exact ND|]. intros x Hx. apply in_map_iff.
  exists (N.to_nat x). split; [apply N2Nat.id|]. apply in_seq. pose proof (H x Hx). lia.
Qed.

Lemma distance_bound : forall B s d p, (forall i j, road dist i j -> (entry dist i j <= B)%Z) ->
  (0 <= B)%Z -> route dist s d p -> (distance dist p <= B * (Z.of_nat (List.length p) - 1))%Z.
Proof.
  intros B s d p HB HB0 H. induction H as [s Hs | s m d p Hr Hp IH]; [simpl; lia|].
  destruct (route_head _ _ _ Hp) as [tl Et]. subst p. rewrite distance_cons2.
  pose proof (HB _ _ Hr). simpl length in *. lia.
Qed.

End G.
End P_G.

(* ================================================================== *)
Section P_FWM.
Import ListNotations.
Open Scope N_scope.

(* Floyd-Warshall on functions: the k-th relaxation and its invariant *)

Section FWM.
Variable dist : list (list Z).
Local Notation nn := (len dist).
Variable INF : Z.

Definition FD (D : N -> N -> Z) (k a b : N) : Z :=
  if (D a k + D k b <? D a b)%Z then (D a k + D k b)%Z else D a b.
Definition FX (D : N -> N -> Z) (X : N -> N -> N) (k a b : N) : N :=
  if (D a k + D k b <? D a b)%Z then X a k else X a b.

Record Inv (k : N) (D : N -> N -> Z) (X : N -> N -> N) : Prop := {
  i_bnd : forall a b, a < nn -> b < nn -> (0 <= D a b <= INF)%Z;
  i_diag : forall a, a < nn -> D a a = 0%Z;
  i_road : forall a b, road dist a b -> (D a b <= entry dist a b)%Z;
  i_succ : forall a b, a < nn -> b < nn -> a <> b -> (D a b < INF)%Z ->
     road dist a (X a b) /\ (entry dist a (X a b) + D (X a b) b <= D a b)%Z;
  i_tri : forall c a b, c < k -> a < nn -> b < nn -> (D a b <= D a c + D c b)%Z
}.

Lemma FD_kk : forall D k a, (0 <= D k k)%Z -> D k k = 0%Z -> FD D k a k = D a k.
Proof using. intros D k a H0 H. unfold FD. rewrite H. destruct (Z.ltb_spec (D a k + 0) (D a k)); lia. Qed.

Lemma FD_kb : forall D k b, D k k = 0%Z -> FD D k k b = D k b.
Proof using. intros D k b H. unfold FD. rewrite H. destruct (Z.ltb_spec (0 + D k b) (D k b)); lia. Qed.

Lemma FD_le : forall D k a b, (FD D k a b <= D a b)%Z.
Proof using. intros. unfold FD. destruct (Z.ltb_spec (D a k + D k b) (D a b)); lia. Qed.

Lemma FD_le2 : forall D k a b, (FD D k a b <= D a k + D k b)%Z.
Proof using. intros. unfold FD. destruct (Z.ltb_spec (D a k + D k b) (D a b)); lia. Qed.

Lemma inv_step : forall k D X, k < nn -> Inv k D X -> Inv (k + 1) (FD D k) (FX D X k).
Proof.
  intros k D X Hk [Hb Hd Hr Hs Ht].
  assert (Hkk : D k k = 0%Z) by (apply Hd; exact Hk).
  constructor.
  - intros a b Ha Hb'. pose proof (FD_le D k a b). pose proof (Hb a b Ha Hb').
    pose proof (Hb a k Ha Hk). pose proof (Hb k b Hk Hb').
    unfold FD in *. destruct (Z.ltb_spec (D a k + D k b) (D a b)); lia.
  - intros a Ha. pose proof (Hb a k Ha Hk). pose proof (Hb k a Hk Ha).
    unfold FD. rewrite (Hd a Ha). destruct (Z.ltb_spec (D a k + D k a) 0); lia.
  - intros a b R. pose proof (FD_le D k a b). pose proof (Hr a b R). lia.
  - intros a b Ha Hb' Nab Hlt. unfold FX.
    destruct (Z.ltb_spec (D a k + D k b) (D a b)) as [L|L].
    + assert (Nak : a <> k) by (intros ->; lia).
      pose proof (Hb k b Hk Hb').
      assert (FDe : FD D k a b = (D a k + D k b)%Z) by (unfold FD; destruct (Z.ltb_spec (D a k + D k b) (D a b)); lia).
      destruct (Hs a k Ha Hk Nak ltac:(lia)) as [R E].
      split; [exact R|]. rewrite FDe. pose proof (FD_le2 D k (X a k) b). lia.
    + assert (FDe : FD D k a b = D a b) by (unfold FD; destruct (Z.ltb_spec (D a k + D k b) (D a b)); lia).
      rewrite FDe in Hlt. destruct (Hs a b Ha Hb' Nab Hlt) as [R E].
      split; [exact R|]. rewrite FDe. pose proof (FD_le D k (X a b) b). lia.
  - intros c a b Hc Ha Hb'.
    assert (Hc' : c < nn) by lia.
    destruct (N.eq_dec c k) as [->|Nck].
    + rewrite FD_kk by (try apply Hb; auto; lia). rewrite FD_kb by exact Hkk. apply FD_le2.
    + assert (Hc2 : c < k) by lia.
      pose proof (Ht c a b Hc2 Ha Hb'). pose proof (Ht c k b Hc2 Hk Hb'). pose proof (Ht c a k Hc2 Ha Hk).
      pose proof (Hb a c Ha Hc'). pose proof (Hb c b Hc' Hb'). pose proof (Hb a k Ha Hk).
      pose proof (Hb k b Hk Hb'). pose proof (Hb k c Hk Hc'). pose proof (Hb c k Hc' Hk).
      pose proof (FD_le D k a b). pose proof (FD_le2 D k a b).
      unfold FD at 2 3.
      destruct (Z.ltb_spec (D a k + D k c) (D a c)); destruct (Z.ltb_spec (D c k + D k b) (D c b)); lia.
Qed.

Lemma inv_route : forall D X, Inv nn D X -> forall s d p, route dist s d p -> (D s d <= distance dist p)%Z.
Proof.
  intros D X I s d p H. induction H as [s Hs | s m d p R Hp IH].
  - rewrite (i_diag _ _ _ I s Hs). simpl. lia.
  - destruct (route_head dist _ _ _ Hp) as [tl Et]. subst p. rewrite distance_cons2.
    pose proof (i_road _ _ _ I s m R). destruct R as (Hs & Hm & _).
    pose proof (route_ends dist _ _ _ Hp) as [_ Hd].
    pose proof (i_tri _ _ _ I m s d Hm Hs Hd). lia.
Qed.

End FWM.
End P_FWM.

(* ================================================================== *)
Section P_FWP.
Open Scope uint63_scope.

Section FWP.
Variable n : int.
Hypothesis Hn : (to_Z n <= 2000)%Z.

Definition dN (A : array int) (a b : N) : Z := to_Z A.[of_Z (Z.of_N a * to_Z n + Z.of_N b)].
Definition xN (A : array int) (a b : N) : N := Z.to_N (dN A a b).
Definition toN (i : int) : N := Z.to_N (to_Z i).

Lemma nn_bound : (to_Z n * to_Z n <= 4000000)%Z.
Proof. pose proof (to_Z_bounded n). nia. Qed.

Lemma idx_val : forall a b : int, (to_Z a < to_Z n)%Z -> (to_Z b < to_Z n)%Z ->
  to_Z (a * n + b) = (to_Z a * to_Z n + to_Z b)%Z.
Proof.
  intros a b Ha Hb. pose proof nn_bound. pose proof (to_Z_bounded a). pose proof (to_Z_bounded b).
  pose proof (to_Z_bounded n).
  assert (to_Z a * to_Z n <= to_Z n * to_Z n)%Z by (apply Z.mul_le_mono_nonneg_r; lia).
  rewrite add_spec, mul_spec. rewrite (Z.mod_small (to_Z a * to_Z n)) by (rewrite wB_val; lia).
  apply Z.mod_small. rewrite wB_val. nia.
Qed.

Lemma get_idx : forall (A : array int) (a b : int), (to_Z a < to_Z n)%Z -> (to_Z b < to_Z n)%Z ->
  A.[a * n + b] = A.[of_Z (Z.of_N (toN a) * to_Z n + Z.of_N (toN b))].
Proof.
  intros A a b Ha Hb. f_equal. apply to_Z_inj. rewrite idx_val by assumption.
  unfold toN. rewrite !Z2N.id by (pose proof (to_Z_bounded a); pose proof (to_Z_bounded b); lia).
  rewrite to_Z_of_Z_small; [reflexivity|]. pose proof nn_bound. pose proof (to_Z_bounded a).
  pose proof (to_Z_bounded b). pose proof (to_Z_bounded n).
  assert (to_Z a * to_Z n <= to_Z n * to_Z n)%Z by (apply Z.mul_le_mono_nonneg_r; lia).
  rewrite wB_val. lia.
Qed.

Lemma ofZN : forall a : N, (Z.of_N a < to_Z n)%Z -> toN (of_Z (Z.of_N a)) = a.
Proof.
  intros a Ha. unfold toN. rewrite to_Z_of_Z_small by (pose proof (to_Z_bounded n); lia). lia.
Qed.

Lemma dN_set : forall (A : array int) (a b : int) v (a' b' : N),
  to_Z (PArray.length A) = (to_Z n * to_Z n)%Z ->
  (to_Z a < to_Z n)%Z -> (to_Z b < to_Z n)%Z -> (Z.of_N a' < to_Z n)%Z -> (Z.of_N b' < to_Z n)%Z ->
  dN (A.[a * n + b <- v]) a' b' = if (N.eqb a' (toN a) && N.eqb b' (toN b))%bool then to_Z v else dN A a' b'.
Proof.
  intros A a b v a' b' HL Ha Hb Ha' Hb'. unfold dN.
  pose proof nn_bound. pose proof (to_Z_bounded a). pose proof (to_Z_bounded b). pose proof (to_Z_bounded n).
  assert (to_Z a * to_Z n <= to_Z n * to_Z n - to_Z n)%Z by nia.
  assert (Z.of_N a' * to_Z n <= to_Z n * to_Z n - to_Z n)%Z by nia.
  destruct (N.eqb_spec a' (toN a)); destruct (N.eqb_spec b' (toN b)); simpl.
  - subst. rewrite <- get_idx by assumption. rewrite gssI; [reflexivity|]. rewrite idx_val by assumption. lia.
  - rewrite gsoZI; [reflexivity|]. rewrite idx_val, to_Z_of_Z_small by (try assumption; rewrite wB_val; lia).
    intros E. apply idx_inj in E; [|lia|lia]. unfold toN in *. lia.
  - rewrite gsoZI; [reflexivity|]. rewrite idx_val, to_Z_of_Z_small by (try assumption; rewrite wB_val; lia).
    intros E. apply idx_inj in E; [|lia|lia]. unfold toN in *. lia.
  - rewrite gsoZI; [reflexivity|]. rewrite idx_val, to_Z_of_Z_small by (try assumption; rewrite wB_val; lia).
    intros E. apply idx_inj in E; [|lia|lia]. unfold toN in *. lia.
Qed.

Lemma fill2_spec : forall g (A : array int), to_Z (PArray.length A) = (to_Z n * to_Z n)%Z ->
  to_Z (PArray.length (fill2 n g A)) = (to_Z n * to_Z n)%Z /\
  forall a b : N, (Z.of_N a < to_Z n)%Z -> (Z.of_N b < to_Z n)%Z ->
    dN (fill2 n g A) a b = to_Z (g (of_Z (Z.of_N a)) (of_Z (Z.of_N b))).
Proof.
  intros g A HL. unfold fill2. pose proof (to_Z_bounded n).
  pose (Iv := fun iz (A' : array int) => to_Z (PArray.length A') = (to_Z n * to_Z n)%Z /\
     forall a b : N, (Z.of_N a < to_Z n)%Z -> (Z.of_N b < to_Z n)%Z ->
       dN A' a b = if Z.ltb (Z.of_N a) iz then to_Z (g (of_Z (Z.of_N a)) (of_Z (Z.of_N b))) else dN A a b).
  match goal with |- context [forl ?lo ?hi ?f ?s0] =>
    assert (Gl : Iv (to_Z hi) (forl lo hi f s0)); [apply (for_invZ Iv); unfold Iv | unfold Iv in Gl] end.
  - change (to_Z 0) with 0%Z. lia.
  - split; [exact HL|]. intros a b Ha Hb. change (to_Z 0) with 0%Z. destruct (Z.ltb_spec (Z.of_N a) 0); [lia|reflexivity].
  - intros i A1 Hi [HL1 P1]. change (to_Z 0) with 0%Z in Hi.
    pose (Jv := fun jz (A' : array int) => to_Z (PArray.length A') = (to_Z n * to_Z n)%Z /\
       forall a b : N, (Z.of_N a < to_Z n)%Z -> (Z.of_N b < to_Z n)%Z ->
         dN A' a b = if (Z.ltb (Z.of_N a) (to_Z i) || (Z.eqb (Z.of_N a) (to_Z i) && Z.ltb (Z.of_N b) jz))%bool
                     then to_Z (g (of_Z (Z.of_N a)) (of_Z (Z.of_N b))) else dN A a b).
    match goal with |- context [forl ?lo ?hi ?f ?s0] =>
      assert (Gj : Jv (to_Z hi) (forl lo hi f s0)); [apply (for_invZ Jv); unfold Jv | unfold Jv in Gj] end.
    + change (to_Z 0) with 0%Z. lia.
    + split; [exact HL1|]. intros a b Ha Hb. rewrite P1 by assumption. change (to_Z 0) with 0%Z.
      destruct (Z.ltb_spec (Z.of_N b) 0); [lia|]. rewrite andb_false_r, orb_false_r. reflexivity.
    + intros j A2 Hj [HL2 P2]. change (to_Z 0) with 0%Z in Hj. split; [rewrite lsetI; exact HL2|].
      intros a b Ha Hb. rewrite dN_set by (try assumption; lia). rewrite P2 by assumption.
      unfold toN.
      destruct (N.eqb_spec a (Z.to_N (to_Z i))); destruct (N.eqb_spec b (Z.to_N (to_Z j))); simpl.
      * subst. rewrite !Z2N.id by lia. rewrite !of_Z_to_Z.
        destruct (Z.ltb_spec (to_Z i) (to_Z i)); [lia|]. rewrite Z.eqb_refl.
        destruct (Z.ltb_spec (to_Z j) (to_Z j + 1)); [reflexivity|lia].
      * destruct (Z.ltb_spec (Z.of_N a) (to_Z i)); [reflexivity|]. simpl.
        destruct (Z.eqb_spec (Z.of_N a) (to_Z i)); [|reflexivity]. simpl.
        destruct (Z.ltb_spec (Z.of_N b) (to_Z j)); destruct (Z.ltb_spec (Z.of_N b) (to_Z j + 1)); try reflexivity; lia.
      * destruct (Z.ltb_spec (Z.of_N a) (to_Z i)); [reflexivity|]. simpl.
        destruct (Z.eqb_spec (Z.of_N a) (to_Z i)); [lia|reflexivity].
      * destruct (Z.ltb_spec (Z.of_N a) (to_Z i)); [reflexivity|]. simpl.
        destruct (Z.eqb_spec (Z.of_N a) (to_Z i)); [lia|reflexivity].
    + destruct Gj as [HL2 P2]. split; [exact HL2|]. intros a b Ha Hb. rewrite P2 by assumption.
      destruct (Z.ltb_spec (Z.of_N a) (to_Z i)); destruct (Z.ltb_spec (Z.of_N a) (to_Z i + 1)); simpl;
        try lia; try reflexivity;
        destruct (Z.eqb_spec (Z.of_N a) (to_Z i)); simpl; try lia;
        destruct (Z.ltb_spec (Z.of_N b) (to_Z n)); try reflexivity; lia.
  - destruct Gl as [HL1 P1]. split; [exact HL1|]. intros a b Ha Hb. rewrite P1 by assumption.
    destruct (Z.ltb_spec (Z.of_N a) (to_Z n)); [reflexivity|lia].
Qed.


Lemma INF_val : to_Z INF = 1073741824%Z.
Proof. reflexivity. Qed.

Definition LenOK (A : array int) : Prop := to_Z (PArray.length A) = (to_Z n * to_Z n)%Z.

Section Iter.
Variables (k : int) (D X : array int).
Hypothesis Hk : (to_Z k < to_Z n)%Z.
Hypothesis HD : LenOK D.
Hypothesis HX : LenOK X.
Hypothesis Hb : forall a b : N, (Z.of_N a < to_Z n)%Z -> (Z.of_N b < to_Z n)%Z ->
  (0 <= dN D a b <= to_Z INF)%Z.
Hypothesis Hkk : dN D (toN k) (toN k) = 0%Z.

Local Notation kN := (toN k).
Local Notation FDk := (FD (dN D) kN).
Local Notation FXk := (FX (dN D) (xN X) kN).

Definition Ist (P : N -> N -> bool) (st : array int * array int) : Prop :=
  LenOK (fst st) /\ LenOK (snd st) /\
  forall a b : N, (Z.of_N a < to_Z n)%Z -> (Z.of_N b < to_Z n)%Z ->
    dN (fst st) a b = (if P a b then FDk a b else dN D a b) /\
    xN (snd st) a b = (if P a b then FXk a b else xN X a b).

Lemma kN_lt : (Z.of_N kN < to_Z n)%Z.
Proof. unfold toN. pose proof (to_Z_bounded k). lia. Qed.

Lemma FD_ik : forall a, (Z.of_N a < to_Z n)%Z -> FDk a kN = dN D a kN.
Proof. intros a Ha. apply FD_kk; [rewrite Hkk; lia | exact Hkk]. Qed.

Lemma FX_ik : forall a, (Z.of_N a < to_Z n)%Z -> FXk a kN = xN X a kN.
Proof.
  intros a Ha. unfold FX. rewrite Hkk.
  destruct (Z.ltb_spec (dN D a kN + 0) (dN D a kN)); [lia | reflexivity].
Qed.

Lemma FD_kj : forall b, FDk kN b = dN D kN b.
Proof. intros b. apply FD_kb. exact Hkk. Qed.

Lemma fw_cell_spec : forall (i j : int) st (P : N -> N -> bool),
  (to_Z i < to_Z n)%Z -> (to_Z j < to_Z n)%Z ->
  Ist P st -> P (toN i) (toN j) = false ->
  Ist (fun a b => P a b || (N.eqb a (toN i) && N.eqb b (toN j)))%bool (fw_cell n k i j st).
Proof.
  intros i j [D' X'] P Hi Hj (HD' & HX' & HP) Pij. simpl in HD', HX', HP.
  pose proof kN_lt as HkN.
  assert (HiN : (Z.of_N (toN i) < to_Z n)%Z) by (unfold toN; pose proof (to_Z_bounded i); lia).
  assert (HjN : (Z.of_N (toN j) < to_Z n)%Z) by (unfold toN; pose proof (to_Z_bounded j); lia).
  assert (Eik : to_Z D'.[i * n + k] = dN D (toN i) kN).
  { rewrite get_idx by assumption. fold (dN D' (toN i) kN). destruct (HP _ _ HiN HkN) as [E1 _].
    rewrite E1. destruct (P (toN i) kN); [apply FD_ik; exact HiN | reflexivity]. }
  assert (Ekj : to_Z D'.[k * n + j] = dN D kN (toN j)).
  { rewrite get_idx by assumption. fold (dN D' kN (toN j)). destruct (HP _ _ HkN HjN) as [E1 _].
    rewrite E1. destruct (P kN (toN j)); [apply FD_kj | reflexivity]. }
  assert (Eij : to_Z D'.[i * n + j] = dN D (toN i) (toN j)).
  { rewrite get_idx by assumption. fold (dN D' (toN i) (toN j)). destruct (HP _ _ HiN HjN) as [E1 _].
    rewrite E1, Pij. reflexivity. }
  assert (Xik : Z.to_N (to_Z X'.[i * n + k]) = xN X (toN i) kN).
  { rewrite get_idx by assumption. fold (dN X' (toN i) kN). fold (xN X' (toN i) kN).
    destruct (HP _ _ HiN HkN) as [_ E1]. rewrite E1. destruct (P (toN i) kN); [apply FX_ik; exact HiN | reflexivity]. }
  pose proof (Hb _ _ HiN HkN). pose proof (Hb _ _ HkN HjN). rewrite INF_val in *.
  assert (Esum : to_Z (D'.[i * n + k] + D'.[k * n + j]) = (dN D (toN i) kN + dN D kN (toN j))%Z).
  { rewrite add_spec, Eik, Ekj. apply Z.mod_small. rewrite wB_val. lia. }
  unfold fw_cell, Ist. simpl fst. simpl snd.
  destruct (D'.[i * n + k] + D'.[k * n + j] <? D'.[i * n + j]) eqn:L.
  - apply Uint63.ltb_spec in L. rewrite Esum, Eij in L. cbn [fst snd].
    split; [unfold LenOK; rewrite lsetI; exact HD'|]. split; [unfold LenOK; rewrite lsetI; exact HX'|].
    intros a b Ha Hb'. simpl. unfold xN. rewrite !dN_set by (try assumption; try lia).
    destruct (HP a b Ha Hb') as [E1 E2]. unfold xN in E2.
    destruct (N.eqb_spec a (toN i)); destruct (N.eqb_spec b (toN j)); simpl; rewrite ?orb_true_r, ?orb_false_r.
    + subst. unfold FD, FX. destruct (Z.ltb_spec (dN D (toN i) kN + dN D kN (toN j)) (dN D (toN i) (toN j))); [|lia].
      split; [exact Esum | exact Xik].
    + exact (conj E1 E2).
    + exact (conj E1 E2).
    + exact (conj E1 E2).
  - apply Bool.not_true_iff_false in L. rewrite Uint63.ltb_spec, Esum, Eij in L. cbn [fst snd].
    split; [exact HD'|]. split; [exact HX'|].
    intros a b Ha Hb'. destruct (HP a b Ha Hb') as [E1 E2]. simpl.
    destruct (N.eqb_spec a (toN i)); destruct (N.eqb_spec b (toN j)); simpl; rewrite ?orb_true_r, ?orb_false_r;
      try exact (conj E1 E2).
    subst. rewrite Pij in E1, E2. unfold FD, FX.
    destruct (Z.ltb_spec (dN D (toN i) kN + dN D kN (toN j)) (dN D (toN i) (toN j))); [lia|].
    exact (conj E1 E2).
Qed.

Lemma fw_iter_spec :
  Ist (fun _ _ => true) (fw_iter n k (D, X)).
Proof.
  unfold fw_iter. pose proof (to_Z_bounded n).
  pose (Iv := fun iz st => Ist (fun a _ => Z.ltb (Z.of_N a) iz) st).
  match goal with |- context [forl ?lo ?hi ?f ?s0] =>
    assert (Gl : Iv (to_Z hi) (forl lo hi f s0)); [apply (for_invZ Iv); unfold Iv | unfold Iv in Gl] end.
  - change (to_Z 0) with 0%Z. lia.
  - split; [exact HD|]. split; [exact HX|]. intros a b _ _. change (to_Z 0) with 0%Z.
    destruct (Z.ltb_spec (Z.of_N a) 0); [lia|]. split; reflexivity.
  - intros i st Hi Pi. change (to_Z 0) with 0%Z in Hi.
    pose (Jv := fun jz st => Ist (fun a b => Z.ltb (Z.of_N a) (to_Z i) ||
                  (Z.eqb (Z.of_N a) (to_Z i) && Z.ltb (Z.of_N b) jz))%bool st).
    match goal with |- context [forl ?lo ?hi ?f ?s0] =>
      assert (Gj : Jv (to_Z hi) (forl lo hi f s0)); [apply (for_invZ Jv); unfold Jv | unfold Jv in Gj] end.
    + change (to_Z 0) with 0%Z. lia.
    + destruct Pi as (P1 & P2 & P3). split; [exact P1|]. split; [exact P2|].
      intros a b Ha Hb'. change (to_Z 0) with 0%Z. destruct (Z.ltb_spec (Z.of_N b) 0); [lia|].
      rewrite andb_false_r, orb_false_r. apply P3; assumption.
    + intros j st' Hj Pj. change (to_Z 0) with 0%Z in Hj.
      assert (Q := fw_cell_spec i j st' _ ltac:(lia) ltac:(lia) Pj).
      destruct Q as (Q1 & Q2 & Q3).
      * unfold toN. rewrite !Z2N.id by lia. destruct (Z.ltb_spec (to_Z i) (to_Z i)); [lia|].
        rewrite Z.eqb_refl. destruct (Z.ltb_spec (to_Z j) (to_Z j)); [lia|]. reflexivity.
      * split; [exact Q1|]. split; [exact Q2|]. intros a b Ha Hb'. rewrite (proj1 (Q3 a b Ha Hb')), (proj2 (Q3 a b Ha Hb')).
        unfold toN. replace (
          ((Z.ltb (Z.of_N a) (to_Z i)) || (Z.eqb (Z.of_N a) (to_Z i)) && (Z.ltb (Z.of_N b) (to_Z j))) ||
          (N.eqb a (Z.to_N (to_Z i))) && (N.eqb b (Z.to_N (to_Z j))))%bool with
          ((Z.ltb (Z.of_N a) (to_Z i)) || (Z.eqb (Z.of_N a) (to_Z i)) && (Z.ltb (Z.of_N b) (to_Z j + 1)))%bool;
          [split; reflexivity|].
        destruct (Z.ltb_spec (Z.of_N a) (to_Z i)); simpl; [reflexivity|].
        destruct (Z.eqb_spec (Z.of_N a) (to_Z i)); simpl.
        -- destruct (N.eqb_spec a (Z.to_N (to_Z i))); [|lia]. simpl.
           destruct (Z.ltb_spec (Z.of_N b) (to_Z j)); destruct (Z.ltb_spec (Z.of_N b) (to_Z j + 1));
             destruct (N.eqb_spec b (Z.to_N (to_Z j))); simpl; try reflexivity; lia.
        -- destruct (N.eqb_spec a (Z.to_N (to_Z i))); [lia|]. reflexivity.
    + destruct Gj as (P1 & P2 & P3). split; [exact P1|]. split; [exact P2|].
      intros a b Ha Hb'. rewrite (proj1 (P3 a b Ha Hb')), (proj2 (P3 a b Ha Hb')).
      replace ((Z.ltb (Z.of_N a) (to_Z i)) || (Z.eqb (Z.of_N a) (to_Z i)) && (Z.ltb (Z.of_N b) (to_Z n)))%bool
        with (Z.ltb (Z.of_N a) (to_Z i + 1)); [split; reflexivity|].
      destruct (Z.ltb_spec (Z.of_N a) (to_Z i)); destruct (Z.ltb_spec (Z.of_N a) (to_Z i + 1));
        destruct (Z.eqb_spec (Z.of_N a) (to_Z i)); destruct (Z.ltb_spec (Z.of_N b) (to_Z n)); simpl;
        try reflexivity; lia.
  - destruct Gl as (P1 & P2 & P3). split; [exact P1|]. split; [exact P2|].
    intros a b Ha Hb'. rewrite (proj1 (P3 a b Ha Hb')), (proj2 (P3 a b Ha Hb')).
    destruct (Z.ltb_spec (Z.of_N a) (to_Z n)); [split; reflexivity | lia].
Qed.

End Iter.

End FWP.
End P_FWP.

(* ================================================================== *)
Section P_FWQ.
Open Scope uint63_scope.

Lemma Inv_ext : forall dist INF k D X D' X', (k <= len dist)%N ->
  (forall a b, a < len dist -> b < len dist -> D' a b = D a b /\ X' a b = X a b)%N ->
  Inv dist INF k D X -> Inv dist INF k D' X'.
Proof.
  intros dist INF k D X D' X' Hk E [Hb Hd Hr Hs Ht]. constructor.
  - intros a b Ha Hb'. rewrite (proj1 (E a b Ha Hb')). apply Hb; assumption.
  - intros a Ha. rewrite (proj1 (E a a Ha Ha)). apply Hd; assumption.
  - intros a b R. pose proof R as (Ha & Hb' & _). rewrite (proj1 (E a b Ha Hb')). apply Hr; assumption.
  - intros a b Ha Hb' Nab Hlt. rewrite (proj1 (E a b Ha Hb')) in *. rewrite (proj2 (E a b Ha Hb')).
    destruct (Hs a b Ha Hb' Nab Hlt) as [R L]. split; [exact R|].
    pose proof R as (_ & Hx & _). rewrite (proj1 (E _ b Hx Hb')). exact L.
  - intros c a b Hc Ha Hb'. assert (Hc' : (c < len dist)%N) by lia.
    rewrite (proj1 (E a b Ha Hb')), (proj1 (E a c Ha Hc')), (proj1 (E c b Hc' Hb')). apply Ht; assumption.
Qed.

Section FWQ.
Variable dist : list (list Z).
Variables (n : int) (W : array int).
Hypothesis Hn : to_Z n = Z.of_N (len dist).
Hypothesis Hn2 : (to_Z n <= 2000)%Z.
Hypothesis HWl : LenOK n W.
Hypothesis HW : forall a b, (a < len dist)%N -> (b < len dist)%N ->
  Sint63.to_Z W.[of_Z (Z.of_N a * to_Z n + Z.of_N b)] = entry dist a b.
Hypothesis Hdiag : forall a, (a < len dist)%N -> entry dist a a = 0%Z.
Hypothesis Hrange : forall a b, (a < len dist)%N -> (b < len dist)%N -> a <> b ->
  entry dist a b = (-1)%Z \/ (1 <= entry dist a b <= 1000)%Z.

Lemma ltn : forall a, (a < len dist)%N -> (Z.of_N a < to_Z n)%Z.
Proof. intros a Ha. rewrite Hn. lia. Qed.

Lemma sint_pos : forall x : int, (0 < Sint63.to_Z x)%Z -> to_Z x = Sint63.to_Z x.
Proof.
  intros x H. rewrite <- zofs_spec in *. unfold zofs in *. rewrite zofi_spec in *.
  destruct (x <? 4611686018427387904) eqn:E; [reflexivity|].
  pose proof (to_Z_bounded x). lia.
Qed.

Lemma isroad_iff : forall a b, (a < len dist)%N -> (b < len dist)%N ->
  isroad W.[of_Z (Z.of_N a * to_Z n + Z.of_N b)] = true <-> road dist a b.
Proof.
  intros a b Ha Hb. unfold isroad, road. rewrite Sint63.ltb_spec, HW by assumption.
  change (Sint63.to_Z 0) with 0%Z. split; [intros H; auto | intros (_ & _ & H); exact H].
Qed.

Lemma fw_spec : LenOK n (fst (fw n W)) /\ LenOK n (snd (fw n W)) /\
  Inv dist (to_Z INF) (len dist) (dN n (fst (fw n W))) (xN n (snd (fw n W))).
Proof.
  unfold fw. cbv zeta. pose proof (to_Z_bounded n).
  assert (Hmk : LenOK n (PArray.make (n * n) 0)).
  { unfold LenOK. pose proof (nn_bound n Hn2). rewrite lmakeI.
    - rewrite mul_spec. apply Z.mod_small. rewrite wB_val. lia.
    - rewrite mul_spec, Z.mod_small by (rewrite wB_val; lia). lia. }
  set (g0 := fun i j => if i =? j then 0 else if isroad W.[i * n + j] then W.[i * n + j] else INF).
  destruct (fill2_spec n Hn2 g0 _ Hmk) as [HD0 PD0].
  destruct (fill2_spec n Hn2 (fun i j => j) _ Hmk) as [HX0 PX0].
  set (D0 := fill2 n g0 (PArray.make (n * n) 0)) in *.
  set (X0 := fill2 n (fun i j => j) (PArray.make (n * n) 0)) in *.
  assert (Hg0 : forall a b, (a < len dist)%N -> (b < len dist)%N ->
     dN n D0 a b = if N.eqb a b then 0%Z else if Z.ltb 0 (entry dist a b) then entry dist a b else to_Z INF).
  { intros a b Ha Hb. rewrite PD0 by (apply ltn; assumption). unfold g0.
    pose proof (ltn a Ha). pose proof (ltn b Hb). clear PD0 PX0 HD0 HX0.
    assert (Ea : to_Z (of_Z (Z.of_N a)) = Z.of_N a) by (apply to_Z_of_Z_small; rewrite wB_val; lia).
    assert (Eb : to_Z (of_Z (Z.of_N b)) = Z.of_N b) by (apply to_Z_of_Z_small; rewrite wB_val; lia).
    destruct (N.eqb_spec a b).
    - subst. rewrite Uint63.eqb_refl. reflexivity.
    - replace (of_Z (Z.of_N a) =? of_Z (Z.of_N b)) with false.
      2:{ symmetry. apply Uint63.eqb_false_spec. intros E. apply (f_equal to_Z) in E. rewrite Ea, Eb in E. lia. }
      rewrite get_idx by (rewrite ?Ea, ?Eb; lia). rewrite (ofZN n) by lia. rewrite (ofZN n) by lia.
      destruct (Z.ltb_spec 0 (entry dist a b)) as [P|P].
      + assert (Hr : isroad W.[of_Z (Z.of_N a * to_Z n + Z.of_N b)] = true)
          by (apply isroad_iff; auto; repeat split; assumption).
        rewrite Hr. rewrite sint_pos; [apply HW; assumption|]. rewrite HW by assumption. exact P.
      + destruct (isroad W.[of_Z (Z.of_N a * to_Z n + Z.of_N b)]) eqn:Hr; [|reflexivity].
        apply isroad_iff in Hr; auto. destruct Hr as (_ & _ & Hr). lia. }
  assert (I0 : Inv dist (to_Z INF) 0 (dN n D0) (xN n X0)).
  { constructor.
    - intros a b Ha Hb. rewrite Hg0 by assumption. rewrite INF_val. clear - Hrange Ha Hb.
      destruct (N.eqb_spec a b) as [Eab|Nab]; [lia|]. destruct (Z.ltb_spec 0 (entry dist a b)); [|lia].
      destruct (Hrange a b Ha Hb Nab); lia.
    - intros a Ha. rewrite Hg0 by assumption. rewrite N.eqb_refl. reflexivity.
    - intros a b (Ha & Hb & Hp). rewrite Hg0 by assumption. clear Hg0 PD0 PX0. destruct (N.eqb_spec a b).
      + subst. rewrite Hdiag in Hp by assumption. exfalso. clear - Hp. lia.
      + clear - Hp. destruct (Z.ltb_spec 0 (entry dist a b)); lia.
    - intros a b Ha Hb Nab Hlt. pose proof (ltn a Ha) as La. pose proof (ltn b Hb) as Lb.
      rewrite Hg0 in Hlt by assumption. rewrite (Hg0 a b Ha Hb).
      destruct (N.eqb_spec a b); [contradiction|].
      assert (Ex : xN n X0 a b = b).
      { unfold xN. rewrite PX0 by assumption. rewrite to_Z_of_Z_small by (rewrite wB_val; clear - Lb Hn2; lia).
        clear; lia. }
      rewrite Ex. destruct (Z.ltb_spec 0 (entry dist a b)) as [P|P]; [|exfalso; clear - Hlt; lia].
      split; [repeat split; assumption|]. rewrite Hg0 by assumption. rewrite N.eqb_refl. clear; lia.
    - intros c a b Hc. exfalso. clear - Hc. lia. }
  clearbody D0 X0. clear Hg0 PD0 PX0 Hmk. clearbody g0.
  pose (Iv := fun kz (st : array int * array int) => LenOK n (fst st) /\ LenOK n (snd st) /\
              Inv dist (to_Z INF) (Z.to_N kz) (dN n (fst st)) (xN n (snd st))).
  match goal with |- context [forl ?lo ?hi ?f ?s0] =>
    assert (Gl : Iv (to_Z hi) (forl lo hi f s0)); [apply (for_invZ Iv); unfold Iv | unfold Iv in Gl] end.
  - change (to_Z 0) with 0%Z. lia.
  - split; [exact HD0|]. split; [exact HX0|]. exact I0.
  - intros k [D X] Hk (HD & HX & Ik). change (to_Z 0) with 0%Z in Hk. simpl fst in *; simpl snd in *.
    assert (HkN : (toN k < len dist)%N) by (unfold toN; lia).
    destruct (fw_iter_spec n Hn2 k D X ltac:(lia) HD HX) as (Q1 & Q2 & Q3).
    + intros a b Ha Hb. apply (i_bnd _ _ _ _ _ Ik); lia.
    + apply (i_diag _ _ _ _ _ Ik). exact HkN.
    + split; [exact Q1|]. split; [exact Q2|].
      replace (Z.to_N (to_Z k + 1)) with (toN k + 1)%N by (unfold toN; lia).
      apply (Inv_ext _ _ _ (FD (dN n D) (toN k)) (FX (dN n D) (xN n X) (toN k))); [lia| |].
      * intros a b Ha Hb. destruct (Q3 a b ltac:(lia) ltac:(lia)) as [E1 E2]. split; assumption.
      * apply inv_step; assumption.
  - destruct Gl as (G1 & G2 & G3). split; [exact G1|]. split; [exact G2|].
    replace (len dist) with (Z.to_N (to_Z n)) by lia. exact G3.
Qed.

End FWQ.
End P_FWQ.

(* ================================================================== *)
Section P_WK.
Open Scope uint63_scope.

Lemma scan_spec : forall (n : int) (W : array int), (to_Z n <= 2000)%Z -> LenOK n W ->
  let I := fst (fst (scan_roads n W)) in let P := snd (fst (scan_roads n W)) in
  let E := snd (scan_roads n W) in
  LenOK n I /\ LenOK n P /\ (to_Z E <= to_Z n * to_Z n)%Z /\
  (forall p, (0 <= p < to_Z n * to_Z n)%Z -> isroad W.[of_Z p] = true ->
     (to_Z I.[of_Z p] < to_Z E)%Z /\ to_Z P.[I.[of_Z p]] = p) /\
  (forall e, (0 <= e < to_Z E)%Z ->
     (0 <= to_Z P.[of_Z e] < to_Z n * to_Z n)%Z /\ isroad W.[P.[of_Z e]] = true /\
     to_Z I.[P.[of_Z e]] = e).
Proof.
  intros n W Hn HW. cbv zeta. unfold scan_roads. pose proof (to_Z_bounded n).
  pose proof (nn_bound n Hn) as Hnn.
  assert (Enn : to_Z (n * n) = (to_Z n * to_Z n)%Z) by (rewrite mul_spec; apply Z.mod_small; rewrite wB_val; lia).
  assert (Hmk : LenOK n (PArray.make (n * n) 0)) by (unfold LenOK; rewrite lmakeI; lia).
  pose (Iv := fun pz (st : array int * array int * int) =>
     let I := fst (fst st) in let P := snd (fst st) in let E := snd st in
     LenOK n I /\ LenOK n P /\ (to_Z E <= pz)%Z /\
     (forall p, (0 <= p < pz)%Z -> isroad W.[of_Z p] = true ->
        (to_Z I.[of_Z p] < to_Z E)%Z /\ to_Z P.[I.[of_Z p]] = p) /\
     (forall e, (0 <= e < to_Z E)%Z ->
        (0 <= to_Z P.[of_Z e] < pz)%Z /\ isroad W.[P.[of_Z e]] = true /\ to_Z I.[P.[of_Z e]] = e)).
  match goal with |- context [forl ?lo ?hi ?f ?s0] =>
    assert (Gl : Iv (to_Z hi) (forl lo hi f s0)); [apply (for_invZ Iv); unfold Iv | unfold Iv in Gl] end.
  - change (to_Z 0) with 0%Z. lia.
  - simpl. split; [exact Hmk|]. split; [exact Hmk|]. change (to_Z 0) with 0%Z.
    split; [lia|]. split; intros; lia.
  - intros p [[I P] e] Hp (HI & HP & He & R1 & R2). simpl in *. change (to_Z 0) with 0%Z in Hp.
    rewrite Enn in Hp. unfold LenOK in HI, HP.
    destruct (isroad W.[p]) eqn:Rp; simpl.
    + assert (Ee : to_Z (e + 1) = (to_Z e + 1)%Z) by (pose proof (to_Z_bounded e); clear - He Hp Hnn; sia).
      split; [unfold LenOK; rewrite lsetI; exact HI|]. split; [unfold LenOK; rewrite lsetI; exact HP|].
      split; [lia|]. split.
      * intros p' Hp' Rp'. destruct (Z.eq_dec p' (to_Z p)) as [Eq|Nq].
        -- subst p'. rewrite of_Z_to_Z. rewrite gssI by lia. rewrite gssI by (pose proof (to_Z_bounded e); lia).
           split; lia.
        -- rewrite gsoZI by (rewrite to_Z_of_Z_small by (rewrite wB_val; lia); lia).
           destruct (R1 p' ltac:(lia) Rp') as [L1 L2].
           rewrite gsoZI by lia. split; [lia | exact L2].
      * intros e' He'. rewrite Ee in He'. destruct (Z.eq_dec e' (to_Z e)) as [Eq|Nq].
        -- subst e'. rewrite of_Z_to_Z. rewrite gssI by (pose proof (to_Z_bounded e); lia).
           split; [pose proof (to_Z_bounded p); lia|]. split; [exact Rp|]. rewrite gssI by lia. reflexivity.
        -- rewrite gsoZI by (rewrite to_Z_of_Z_small by (rewrite wB_val; lia); lia).
           destruct (R2 e' ltac:(lia)) as (L1 & L2 & L3). split; [lia|]. split; [exact L2|].
           rewrite gsoZI by lia. exact L3.
    + split; [exact HI|]. split; [exact HP|]. split; [lia|]. split.
      * intros p' Hp' Rp'. destruct (Z.eq_dec p' (to_Z p)) as [Eq|Nq].
        -- subst p'. rewrite of_Z_to_Z in Rp'. congruence.
        -- apply R1; [lia | exact Rp'].
      * intros e' He'. destruct (R2 e' He') as (L1 & L2 & L3). split; [lia|]. auto.
  - rewrite Enn in Gl. exact Gl.
Qed.

Fixpoint psumR (f : N -> N -> R) (p : list N) : R :=
  match p with
  | a :: ((b :: _) as tl) => (f a b + psumR f tl)%R
  | _ => 0%R
  end.

Definition cntsum (E : int) (cnt : array int) (z : nat -> R) : R :=
  sumR (Z.to_nat (to_Z E)) (fun e => (IZR (to_Z cnt.[of_Z (Z.of_nat e)]) * z e)%R).

Lemma cntsum_incr : forall E cnt (e : int) z,
  to_Z (PArray.length cnt) = to_Z E ->
  (to_Z e < to_Z E)%Z -> (to_Z cnt.[e] + 1 < wB)%Z ->
  cntsum E (cnt.[e <- cnt.[e] + 1]) z = (cntsum E cnt z + z (Z.to_nat (to_Z e)))%R.
Proof.
  intros E cnt e z HL He Hb. unfold cntsum.
  rewrite (sumR_ext _ _ (fun e' => (IZR (to_Z cnt.[of_Z (Z.of_nat e')]) * z e' +
              (if Nat.eqb e' (Z.to_nat (to_Z e)) then z e' else 0))%R)).
  - rewrite sumR_plus, sumR_delta. destruct (Nat.ltb_spec (Z.to_nat (to_Z e)) (Z.to_nat (to_Z E))); [reflexivity|].
    pose proof (to_Z_bounded e). lia.
  - intros e' He'. destruct (Nat.eqb_spec e' (Z.to_nat (to_Z e))) as [Eq|Nq].
    + subst e'. rewrite Z2Nat.id by (pose proof (to_Z_bounded e); lia). rewrite of_Z_to_Z.
      rewrite gssI by lia. rewrite add_spec, Z.mod_small by (pose proof (to_Z_bounded cnt.[e]); lia).
      change (to_Z 1) with 1%Z. rewrite plus_IZR. ring.
    + rewrite gsoZI. 2:{ rewrite to_Z_of_Z_small by (rewrite wB_val; pose proof (to_Z_bounded E); lia). lia. }
      ring.
Qed.

Lemma walk_eq : forall n d E D X I cur cnt H,
  walk n d E D X I cur cnt H =
  if cur =? d then cnt else
  let v := X.[cur * n + d] in
  match bdec (D.[v * n + d] <? D.[cur * n + d]) with
  | left Hlt =>
      let e := I.[cur * n + v] in
      walk n d E D X I v (if e <? E then cnt.[e <- cnt.[e] + 1] else cnt)
        (Acc_inv H (walk_dec _ _ Hlt))
  | right _ => cnt
  end.
Proof. intros. destruct H. reflexivity. Qed.

Section Walk.
Variable dist : list (list Z).
Variables (n E : int) (D X I : array int).
Hypothesis Hn : to_Z n = Z.of_N (len dist).
Hypothesis Hn2 : (to_Z n <= 2000)%Z.
Hypothesis HI : Inv dist (to_Z INF) (len dist) (dN n D) (xN n X).
Hypothesis HIr : forall a b, road dist a b -> (to_Z I.[of_Z (Z.of_N a * to_Z n + Z.of_N b)] < to_Z E)%Z.

Lemma toN_lt : forall c : int, (to_Z c < to_Z n)%Z -> (toN c < len dist)%N.
Proof. intros c H. unfold toN. pose proof (to_Z_bounded c). lia. Qed.

Lemma walk_spec : forall (d : int), (to_Z d < to_Z n)%Z -> forall B, (B <= to_Z INF)%Z ->
  forall mz cur cnt H, to_Z D.[cur * n + d] = mz ->
  (to_Z cur < to_Z n)%Z -> (dN n D (toN cur) (toN d) < to_Z INF)%Z ->
  to_Z (PArray.length cnt) = to_Z E ->
  (forall e, (0 <= e < to_Z E)%Z -> (0 <= to_Z cnt.[of_Z e] <= B - dN n D (toN cur) (toN d))%Z) ->
  exists p, route dist (toN cur) (toN d) p /\
    (distance dist p <= dN n D (toN cur) (toN d))%Z /\
    to_Z (PArray.length (walk n d E D X I cur cnt H)) = to_Z E /\
    (forall e, (0 <= e < to_Z E)%Z -> (0 <= to_Z (walk n d E D X I cur cnt H).[of_Z e] <= B)%Z) /\
    forall z, cntsum E (walk n d E D X I cur cnt H) z =
      (cntsum E cnt z + psumR (fun a b => z (Z.to_nat (dN n I a b))) p)%R.
Proof.
  intros d Hd B HB mz. induction mz as [mz IH] using (well_founded_induction (Zwf_well_founded 0)).
  intros cur cnt H Emz Hc Hlt HL Hcnt.
  pose proof (toN_lt cur Hc) as HcN. pose proof (toN_lt d Hd) as HdN.
  pose proof (i_bnd _ _ _ _ _ HI _ _ HcN HdN) as Bcd.
  rewrite walk_eq.
  destruct (cur =? d) eqn:Ecd.
  - apply Uint63.eqb_spec in Ecd. subst cur. exists (toN d :: nil). split; [apply route_here; exact HdN|].
    split; [simpl; lia|]. split; [exact HL|]. split.
    + intros e He. pose proof (Hcnt e He). lia.
    + intros z. simpl. ring.
  - apply Uint63.eqb_false_spec in Ecd.
    assert (Ncd : toN cur <> toN d).
    { intros E'. apply Ecd. apply to_Z_inj. unfold toN in E'. pose proof (to_Z_bounded cur).
      pose proof (to_Z_bounded d). lia. }
    destruct (i_succ _ _ _ _ _ HI _ _ HcN HdN Ncd Hlt) as [R Le].
    cbv zeta.
    set (v := X.[cur * n + d]).
    assert (Ev : xN n X (toN cur) (toN d) = toN v).
    { unfold xN, dN, v, toN. rewrite get_idx by assumption. reflexivity. }
    rewrite Ev in R, Le.
    assert (Hv : (to_Z v < to_Z n)%Z) by (destruct R as (_ & Hv & _); unfold toN in Hv; pose proof (to_Z_bounded v); lia).
    pose proof (toN_lt v Hv) as HvN.
    assert (Edv : to_Z D.[v * n + d] = dN n D (toN v) (toN d)) by (unfold dN; rewrite get_idx by assumption; reflexivity).
    assert (Edc : to_Z D.[cur * n + d] = dN n D (toN cur) (toN d)) by (unfold dN; rewrite get_idx by assumption; reflexivity).
    pose proof R as (_ & _ & Rp).
    destruct (bdec (D.[v * n + d] <? D.[cur * n + d])) as [Hlt'|Hlt'].
    2:{ exfalso. rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec, Edv, Edc in Hlt'. lia. }
    cbv zeta. set (e := I.[cur * n + v]).
    assert (He : (to_Z e < to_Z E)%Z).
    { unfold e. rewrite get_idx by assumption. apply HIr. exact R. }
    replace (e <? E) with true by (symmetry; apply Uint63.ltb_spec; exact He).
    pose proof (to_Z_bounded e) as Be.
    assert (Bce : (0 <= to_Z cnt.[e] <= B - dN n D (toN cur) (toN d))%Z).
    { rewrite <- (of_Z_to_Z e). apply Hcnt. lia. }
    assert (Ece : to_Z (cnt.[e] + 1) = (to_Z cnt.[e] + 1)%Z).
    { rewrite add_spec. apply Z.mod_small. rewrite wB_val. rewrite INF_val in *. lia. }
    pose proof (i_bnd _ _ _ _ _ HI _ _ HvN HdN) as Bvd.
    destruct (IH (to_Z D.[v * n + d])) with (cur := v) (cnt := cnt.[e <- cnt.[e] + 1])
       (H := Acc_inv H (walk_dec D.[v * n + d] D.[cur * n + d] Hlt')) as (p' & R' & L' & HL' & Hc' & Hs').
    + rewrite <- Emz, Edv, Edc. unfold Zwf. lia.
    + reflexivity.
    + exact Hv.
    + lia.
    + rewrite lsetI. exact HL.
    + intros e' He'. destruct (Z.eq_dec e' (to_Z e)) as [Eq|Nq].
      * subst e'. rewrite of_Z_to_Z, gssI by lia. lia.
      * rewrite gsoZI by (rewrite to_Z_of_Z_small by (rewrite wB_val; lia); lia).
        pose proof (Hcnt e' He'). lia.
    + exists (toN cur :: p'). split; [apply route_step with (toN v); assumption|].
      destruct (route_head dist _ _ _ R') as [tl Et].
      split; [rewrite Et in *; rewrite distance_cons2; lia|].
      split; [exact HL'|]. split; [exact Hc'|].
      intros z. rewrite Hs'. rewrite cntsum_incr by (try exact HL; try lia).
      rewrite Et. simpl psumR.
      assert (Ei : dN n I (toN cur) (toN v) = to_Z e) by (unfold dN, e; rewrite get_idx by assumption; reflexivity).
      rewrite Ei. ring.
Qed.

End Walk.
End P_WK.

(* ================================================================== *)
Section P_MS1.
Open Scope uint63_scope.

Section MS1.
Variables (dist : list (list Z)) (rs rd rt qs qd : list N).
Variables (xdist : array (array sint)) (xrs xrd xrt xqs xqd : array uint).
Hypothesis Hv : valid_input dist rs rd rt qs qd.
Hypothesis Rd : repr xdist dist.

Local Notation n := (PArray.length xdist).
Local Notation nn := (len dist).
Local Notation W := (flatten (PArray.length xdist) xdist).

Lemma n_val : to_Z n = Z.of_N nn.
Proof. destruct Rd as [L _]. unfold len. rewrite nat_N_Z. symmetry. exact L. Qed.

Lemma n_bounds : (1 <= to_Z n <= 30)%Z.
Proof. rewrite n_val. destruct (vi_n _ _ _ _ _ _ Hv). lia. Qed.

Lemma n_le : (to_Z n <= 2000)%Z.
Proof. pose proof n_bounds. lia. Qed.

Lemma entry_repr : forall a b, (a < nn)%N -> (b < nn)%N ->
  Sint63.to_Z ((xdist.[of_Z (Z.of_N a)]).[of_Z (Z.of_N b)] : sint) = entry dist a b.
Proof.
  intros a b Ha Hb. destruct Rd as [L Hc].
  unfold len in Ha, Hb.
  destruct (Hc (N.to_nat a) ltac:(lia)) as (row & Er & Rr).
  pose proof (vi_rows _ _ _ _ _ _ Hv) as Rows. rewrite Forall_forall in Rows.
  assert (Hrow : len row = nn) by (apply Rows; apply nth_error_In with (N.to_nat a); exact Er).
  destruct Rr as [Lr Hcr].
  unfold len in Hrow.
  destruct (Hcr (N.to_nat b) ltac:(lia)) as (e & Ee & Re).
  unfold repr, repr_sint in Re.
  rewrite N_nat_Z in Re. rewrite N_nat_Z in Re.
  unfold entry. rewrite (nth_error_nth _ _ _ Er). rewrite (nth_error_nth _ _ _ Ee). exact Re.
Qed.

Lemma W_len : LenOK n W.
Proof.
  unfold flatten. destruct (fill2_spec n n_le (fun i j => (xdist.[i]).[j]) (PArray.make (n * n) 0)) as [L _].
  - pose proof n_bounds. pose proof (nn_bound n n_le). unfold LenOK. rewrite lmakeI.
    + rewrite mul_spec. apply Z.mod_small. rewrite wB_val. lia.
    + rewrite mul_spec, Z.mod_small by (rewrite wB_val; lia). lia.
  - exact L.
Qed.

Lemma W_spec : forall a b, (a < nn)%N -> (b < nn)%N ->
  Sint63.to_Z W.[of_Z (Z.of_N a * to_Z n + Z.of_N b)] = entry dist a b.
Proof.
  intros a b Ha Hb. unfold flatten.
  match goal with |- context [fill2 ?n0 ?g ?A] =>
    destruct (fill2_spec n0 n_le g A) as [_ P] end.
  - pose proof n_bounds. pose proof (nn_bound n n_le). unfold LenOK. rewrite lmakeI.
    + rewrite mul_spec. apply Z.mod_small. rewrite wB_val. lia.
    + rewrite mul_spec, Z.mod_small by (rewrite wB_val; lia). lia.
  - pose proof n_val. specialize (P a b ltac:(lia) ltac:(lia)). unfold dN in P.
    apply to_Z_inj in P. rewrite P. exact (entry_repr a b Ha Hb).
Qed.


Local Notation D := (fst (fw (PArray.length xdist) W)).
Local Notation X := (snd (fw (PArray.length xdist) W)).
Local Notation I := (fst (fst (scan_roads (PArray.length xdist) W))).
Local Notation P := (snd (fst (scan_roads (PArray.length xdist) W))).
Local Notation E := (snd (scan_roads (PArray.length xdist) W)).

Lemma Hdiag : forall a, (a < nn)%N -> entry dist a a = 0%Z.
Proof. intros a Ha. apply (vi_diag _ _ _ _ _ _ Hv). exact Ha. Qed.

Lemma Hrange : forall a b, (a < nn)%N -> (b < nn)%N -> a <> b ->
  entry dist a b = (-1)%Z \/ (1 <= entry dist a b <= 1000)%Z.
Proof. intros a b Ha Hb Nab. apply (vi_dist _ _ _ _ _ _ Hv); assumption. Qed.

Lemma FWinv : Inv dist (to_Z INF) nn (dN n D) (xN n X).
Proof. apply (fw_spec dist n W n_val n_le W_spec Hdiag Hrange). Qed.

Lemma road_le : forall a b, road dist a b -> (1 <= entry dist a b <= 1000)%Z.
Proof.
  intros a b (Ha & Hb & Hp). destruct (N.eq_dec a b) as [->|Nab].
  - rewrite Hdiag in Hp by exact Ha. lia.
  - destruct (Hrange a b Ha Hb Nab); lia.
Qed.

Lemma scan_facts :
  LenOK n I /\ LenOK n P /\ (to_Z E <= to_Z n * to_Z n)%Z /\
  (forall p, (0 <= p < to_Z n * to_Z n)%Z -> isroad W.[of_Z p] = true ->
     (to_Z I.[of_Z p] < to_Z E)%Z /\ to_Z P.[I.[of_Z p]] = p) /\
  (forall e, (0 <= e < to_Z E)%Z ->
     (0 <= to_Z P.[of_Z e] < to_Z n * to_Z n)%Z /\ isroad W.[P.[of_Z e]] = true /\
     to_Z I.[P.[of_Z e]] = e).
Proof. apply (scan_spec n W n_le W_len). Qed.

Lemma E_le : (to_Z E <= 900)%Z.
Proof. destruct scan_facts as (_ & _ & H & _). pose proof n_bounds. nia. Qed.

Lemma pos_lt : forall a b, (a < nn)%N -> (b < nn)%N ->
  (0 <= Z.of_N a * to_Z n + Z.of_N b < to_Z n * to_Z n)%Z.
Proof. intros a b Ha Hb. pose proof n_val. nia. Qed.

Lemma HIr : forall a b, road dist a b -> (to_Z I.[of_Z (Z.of_N a * to_Z n + Z.of_N b)] < to_Z E)%Z.
Proof.
  intros a b R. pose proof R as (Ha & Hb & _). destruct scan_facts as (_ & _ & _ & S1 & _).
  apply S1; [apply pos_lt; assumption|]. apply (isroad_iff dist n W W_spec); assumption.
Qed.

Lemma shortest_bound : forall s d p, shortest_route dist s d p ->
  (distance dist p <= 1000 * (Z.of_N nn - 1))%Z.
Proof.
  intros s d p Sh. pose proof (shortest_nodup dist s d p Sh) as ND.
  destruct Sh as [R _].
  pose proof (nodup_length p nn ND (route_cities dist _ _ _ R)) as L.
  pose proof (distance_bound dist 1000 s d p (fun i j H => proj2 (road_le i j H)) ltac:(lia) R) as B.
  destruct (route_head dist _ _ _ R) as [tl ->]. simpl length in *. nia.
Qed.

Lemma route_cnt_spec : forall s d : int, (toN s < nn)%N -> (toN d < nn)%N ->
  unique_shortest_route dist (toN s) (toN d) ->
  let cnt := route_cnt n E D X I s d in
  to_Z (PArray.length cnt) = to_Z E /\
  (forall e, (0 <= e < to_Z E)%Z -> (0 <= to_Z cnt.[of_Z e] <= to_Z INF)%Z) /\
  exists p, shortest_route dist (toN s) (toN d) p /\ distance dist p = dN n D (toN s) (toN d) /\
    (forall p', shortest_route dist (toN s) (toN d) p' -> p' = p) /\
    forall z, cntsum E cnt z = psumR (fun a b => z (Z.to_nat (dN n I a b))) p.
Proof.
  intros s d Hs Hd (p0 & Sh0 & Un0). cbv zeta.
  pose proof FWinv as FI. pose proof n_val as En. pose proof E_le as HE.
  assert (Hs' : (to_Z s < to_Z n)%Z) by (unfold toN in Hs; pose proof (to_Z_bounded s); lia).
  assert (Hd' : (to_Z d < to_Z n)%Z) by (unfold toN in Hd; pose proof (to_Z_bounded d); lia).
  assert (Dle : (dN n D (toN s) (toN d) <= distance dist p0)%Z) by (apply (inv_route dist _ _ _ FI); apply Sh0).
  pose proof (shortest_bound _ _ _ Sh0) as Bp0.
  assert (Dlt : (dN n D (toN s) (toN d) < to_Z INF)%Z).
  { rewrite INF_val. destruct (vi_n _ _ _ _ _ _ Hv). lia. }
  assert (HLm : to_Z (PArray.length (PArray.make E 0)) = to_Z E) by (rewrite lmakeI; [reflexivity | lia]).
  unfold route_cnt.
  destruct (walk_spec dist n E D X I n_val n_le FI HIr d Hd' (to_Z INF) ltac:(lia)
              (to_Z D.[s * n + d]) s (PArray.make E 0) (Zwf_well_founded 0 _) eq_refl Hs' Dlt HLm)
    as (p & R & Ld & HL & Hc & Hsum).
  - intros e He. rewrite gmakeI. change (to_Z 0) with 0%Z. pose proof (i_bnd _ _ _ _ _ FI _ _ Hs Hd). lia.
  - split; [exact HL|]. split; [exact Hc|].
    assert (Shp : shortest_route dist (toN s) (toN d) p).
    { split; [exact R|]. intros p' R'. pose proof (inv_route dist _ _ _ FI _ _ _ R'). lia. }
    exists p. split; [exact Shp|]. split.
    + pose proof (inv_route dist _ _ _ FI _ _ _ R). lia.
    + split.
      * intros p' Sh'. rewrite (Un0 p' Sh'), (Un0 p Shp). reflexivity.
      * intros z. rewrite Hsum. unfold cntsum. rewrite sumR_zero; [ring|].
        intros e He. rewrite gmakeI. change (to_Z 0) with 0%Z. simpl. ring.
Qed.

End MS1.
End P_MS1.

(* ================================================================== *)
Section P_MS2.
Open Scope uint63_scope.

(* the rows of the initial tableau, read as linear forms *)
Section Rows.
Variables (n E RR : int) (W D X I P rs rd rt : array int).
Hypothesis Hg : guard E RR = true.
Local Notation Et := (Z.to_nat (to_Z E)).
Local Notation Rt := (Z.to_nat (to_Z RR)).
Local Notation w := (E + (E + RR) + 1).
Local Notation T0 := (build_T n E RR W D X I P rs rd rt).
Local Notation t0 := (cell (build_T n E RR W D X I P rs rd rt) (E + (E + RR) + 1)).

Lemma mn_val : Z.to_nat (to_Z (E + RR)) = (Et + Rt)%nat.
Proof. rewrite (m_val E RR Hg). pose proof (to_Z_bounded E). pose proof (to_Z_bounded RR). lia. Qed.

Lemma Nn_val : Z.of_nat (Et + (Et + Rt)) = to_Z (E + (E + RR)).
Proof. rewrite (N_val' E RR Hg). pose proof (to_Z_bounded E). pose proof (to_Z_bounded RR). lia. Qed.

Lemma t0_eq : forall r j, (r < Et + Rt)%nat -> (j <= Et + (Et + Rt))%nat ->
  t0 r j = T0f n E RR W D X I P rs rd rt (Z.of_nat r) (Z.of_nat j).
Proof.
  intros r j Hr Hj. unfold cell. destruct (build_spec n E RR W D X I P rs rd rt Hg) as [_ PT].
  apply PT. unfold IR. rewrite (m_val E RR Hg), (w_val' E RR Hg).
  pose proof (to_Z_bounded E). pose proof (to_Z_bounded RR). lia.
Qed.

Definition cnt_k (k : nat) : array int := cntk n E D X I rs rd (Z.of_nat k).
Definition b_k (k : nat) : Z := bk n D rs rd rt (Z.of_nat k).
Definition sg (b : Z) : R := if Z.ltb b 0 then (-1)%R else 1%R.

Lemma lin_bound : forall e z, (e < Et)%nat ->
  lin (Et + Rt) Et (t0 e) z = (z e + z (Et + e)%nat)%R.
Proof.
  intros e z He. unfold lin. replace (Et + (Et + Rt))%nat with (Et + (Et + Rt))%nat by lia.
  rewrite (sumR_ext _ _ (fun j => (if Nat.eqb j e then z j else 0) + (if Nat.eqb j (Et + e) then z j else 0))%R).
  - rewrite sumR_plus, !sumR_delta.
    destruct (Nat.ltb_spec e (Et + (Et + Rt))); [|lia]. destruct (Nat.ltb_spec (Et + e) (Et + (Et + Rt))); [|lia].
    reflexivity.
  - intros j Hj. rewrite t0_eq by lia. unfold T0f, boundf.
    pose proof (to_Z_bounded E). pose proof Nn_val.
    destruct (Z.ltb_spec (Z.of_nat e) (to_Z E)); [|lia].
    destruct (Nat.eqb_spec j e); destruct (Nat.eqb_spec j (Et + e)); try lia.
    + subst. rewrite Z.eqb_refl. ring.
    + destruct (Z.eqb_spec (Z.of_nat j) (Z.of_nat e)); [lia|].
      destruct (Z.eqb_spec (Z.of_nat j) (to_Z E + Z.of_nat e)); [|lia]. ring.
    + destruct (Z.eqb_spec (Z.of_nat j) (Z.of_nat e)); [lia|].
      destruct (Z.eqb_spec (Z.of_nat j) (to_Z E + Z.of_nat e)); [lia|].
      destruct (Z.eqb_spec (Z.of_nat j) (to_Z (E + (E + RR)))); [lia|]. ring.
Qed.

Lemma rhs_bound : forall e, (e < Et)%nat -> t0 e (Et + (Et + Rt)) = IZR (ue W P (Z.of_nat e)).
Proof.
  intros e He. rewrite t0_eq by lia. unfold T0f, boundf. rewrite Nn_val.
  pose proof (to_Z_bounded E). pose proof (N_val' E RR Hg).
  destruct (Z.ltb_spec (Z.of_nat e) (to_Z E)); [|lia].
  destruct (Z.eqb_spec (to_Z (E + (E + RR))) (Z.of_nat e)); [lia|].
  destruct (Z.eqb_spec (to_Z (E + (E + RR))) (to_Z E + Z.of_nat e)); [lia|].
  rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma lin_deliv : forall k z, (k < Rt)%nat ->
  lin (Et + Rt) Et (t0 (Et + k)) z =
  (sg (b_k k) * cntsum E (cnt_k k) z + z (Et + Et + k)%nat)%R.
Proof.
  intros k z Hk. unfold lin. pose proof (to_Z_bounded E). pose proof (to_Z_bounded RR). pose proof Nn_val.
  rewrite (sumR_ext _ _ (fun j => (if Nat.ltb j Et then sg (b_k k) * (IZR (to_Z (cnt_k k).[of_Z (Z.of_nat j)]) * z j) else 0) +
                                   (if Nat.eqb j (Et + Et + k) then z j else 0))%R).
  - rewrite sumR_plus, sumR_delta. destruct (Nat.ltb_spec (Et + Et + k) (Et + (Et + Rt))); [|lia].
    f_equal. unfold cntsum. rewrite <- sumR_scal.
    replace (Et + (Et + Rt))%nat with (Et + (Et + Rt))%nat by reflexivity.
    rewrite sumR_split. rewrite (sumR_zero (Et + Rt)) by (intros i Hi; destruct (Nat.ltb_spec (Et + i) Et); [lia|reflexivity]).
    rewrite Rplus_0_r. apply sumR_ext. intros j Hj. destruct (Nat.ltb_spec j Et); [reflexivity|lia].
  - intros j Hj. rewrite t0_eq by lia. unfold T0f, delivf.
    destruct (Z.ltb_spec (Z.of_nat (Et + k)) (to_Z E)); [lia|].
    replace (Z.of_nat (Et + k) - to_Z E)%Z with (Z.of_nat k) by lia.
    fold (cnt_k k). unfold cntk. fold (b_k k).
    destruct (Nat.ltb_spec j Et); destruct (Nat.eqb_spec j (Et + Et + k)); try lia.
    + destruct (Z.ltb_spec (Z.of_nat j) (to_Z E)); [|lia]. unfold sg, b_k. rewrite zofi_spec.
      destruct (Z.ltb (bk n D rs rd rt (Z.of_nat k)) 0); rewrite ?opp_IZR; ring.
    + subst j. destruct (Z.ltb_spec (Z.of_nat (Et + Et + k)) (to_Z E)); [lia|].
      destruct (Z.eqb_spec (Z.of_nat (Et + Et + k)) (to_Z E + to_Z E + Z.of_nat k)); [|lia]. ring.
    + destruct (Z.ltb_spec (Z.of_nat j) (to_Z E)); [lia|].
      destruct (Z.eqb_spec (Z.of_nat j) (to_Z E + to_Z E + Z.of_nat k)); [lia|].
      destruct (Z.eqb_spec (Z.of_nat j) (to_Z (E + (E + RR)))); [lia|]. ring.
Qed.

Lemma rhs_deliv : forall k, (k < Rt)%nat -> t0 (Et + k) (Et + (Et + Rt)) = IZR (Z.abs (b_k k)).
Proof.
  intros k Hk. rewrite t0_eq by lia. unfold T0f, delivf. rewrite Nn_val.
  pose proof (to_Z_bounded E). pose proof (to_Z_bounded RR). pose proof (N_val' E RR Hg).
  destruct (Z.ltb_spec (Z.of_nat (Et + k)) (to_Z E)); [lia|].
  destruct (Z.ltb_spec (to_Z (E + (E + RR))) (to_Z E)); [lia|].
  destruct (Z.eqb_spec (to_Z (E + (E + RR))) (to_Z E + to_Z E + (Z.of_nat (Et + k) - to_Z E))); [lia|].
  rewrite Z.eqb_refl. unfold b_k. f_equal. f_equal. f_equal. lia.
Qed.

End Rows.

Lemma duration_cons2 : forall dist v a b l,
  duration dist v (a :: b :: l) = (60 * IZR (entry dist a b) / v a b + duration dist v (b :: l))%R.
Proof. reflexivity. Qed.

Lemma dur_gen : forall dist (v : N -> N -> R) (f : N -> N -> R),
  (forall a b, road dist a b -> (60 * IZR (entry dist a b) / v a b = IZR (entry dist a b) + f a b)%R) ->
  forall s d p, route dist s d p -> duration dist v p = (IZR (distance dist p) + psumR f p)%R.
Proof.
  intros dist v f Hf s d p R. induction R as [s Hs | s m d p Rr Rp IH].
  - simpl. ring.
  - destruct (route_head dist _ _ _ Rp) as [tl ->]. rewrite duration_cons2, distance_cons2.
    simpl psumR. rewrite Hf by exact Rr. rewrite IH, plus_IZR. simpl psumR. ring.
Qed.

Lemma repr_uint_nth : forall (x : array uint) (l : list N), repr x l ->
  forall k : nat, (k < List.length l)%nat ->
  Z.to_N (to_Z x.[of_Z (Z.of_nat k)]) = get_list_N l (N.of_nat k).
Proof.
  intros x l [L H] k Hk. destruct (H k Hk) as (v & Ev & Rv). unfold repr, repr_uint in Rv.
  unfold get_list_N. rewrite Nat2N.id. rewrite (nth_error_nth _ _ _ Ev). exact Rv.
Qed.

Lemma repr_uint_len : forall (x : array uint) (l : list N), repr x l ->
  to_Z (PArray.length x) = Z.of_N (len l).
Proof. intros x l [L _]. unfold len. rewrite nat_N_Z. symmetry. exact L. Qed.
End P_MS2.

(* ================================================================== *)
Section P_FL.
Import Flocq.Core.Raux Flocq.Core.Zaux.
Local Open Scope R_scope.

Lemma two36_R : IZR (to_Z two36) = 68719476736.
Proof. reflexivity. Qed.

Lemma q2f_spec : forall q, 0 <= Q2R q <= 60000 ->
  exists r, repr (q2f q) r /\ Rabs (r - Q2R q) <= / 1000000.
Proof.
  intros [num den] Hq. unfold q2f. simpl Qnum. simpl Qden.
  set (mz := ((num * 68719476736) / Zpos den)%Z).
  assert (Hd : (0 < Zpos den)%Z) by lia.
  assert (Lo : (mz * Zpos den <= num * 68719476736)%Z) by (unfold mz; rewrite Z.mul_comm; apply Z.mul_div_le; lia).
  assert (Hi : (num * 68719476736 < (mz + 1) * Zpos den)%Z).
  { unfold mz. rewrite Z.mul_comm. pose proof (Z.mul_succ_div_gt (num * 68719476736) (Zpos den) Hd). lia. }
  unfold Q2R in Hq. simpl in Hq.
  assert (Dp : 0 < IZR (Zpos den)) by (apply IZR_lt; lia).
  set (y := IZR num * / IZR (Zpos den)) in *.
  assert (Ylo : IZR mz <= y * 68719476736).
  { apply (Rmult_le_reg_r (IZR (Zpos den))); [exact Dp|]. unfold y.
    replace (IZR num * / IZR (Z.pos den) * 68719476736 * IZR (Z.pos den)) with (IZR (num * 68719476736))
      by (rewrite mult_IZR; field; lra).
    rewrite <- mult_IZR. apply IZR_le. exact Lo. }
  assert (Yhi : y * 68719476736 < IZR mz + 1).
  { apply (Rmult_lt_reg_r (IZR (Zpos den))); [exact Dp|]. unfold y.
    replace (IZR num * / IZR (Z.pos den) * 68719476736 * IZR (Z.pos den)) with (IZR (num * 68719476736))
      by (rewrite mult_IZR; field; lra).
    replace ((IZR mz + 1) * IZR (Z.pos den)) with (IZR ((mz + 1) * Z.pos den)) by (rewrite mult_IZR, plus_IZR; ring).
    apply IZR_lt. exact Hi. }
  assert (Mb : (0 <= mz < 4503599627370496)%Z).
  { split.
    - destruct (Z_lt_le_dec mz 0) as [L|L]; [|exact L]. exfalso.
      assert (IZR mz <= -1) by (apply IZR_le; lia). lra.
    - apply lt_IZR. assert (y * 68719476736 <= 60000 * 68719476736) by lra. lra. }
  assert (Ei : to_Z (iofz mz) = mz) by (apply iofz_spec; rewrite wB_val; lia).
  assert (Ra : repr (of_uint63 (iofz mz)) (IZR mz)).
  { pose proof (repr_of_uint63_exact (iofz mz) ltac:(rewrite Ei; lia)) as R0. rewrite Ei in R0. exact R0. }
  assert (Rb : repr (of_uint63 two36) 68719476736).
  { rewrite <- two36_R. apply repr_of_uint63_exact. reflexivity. }
  set (t := IZR mz / 68719476736).
  assert (Tb : 0 <= t <= 60000).
  { unfold t. split.
    - apply Rmult_le_pos; [apply IZR_le; lia | lra].
    - apply (Rmult_le_reg_r 68719476736); [lra|]. field_simplify. lra. }
  exists (rnd t). split.
  - apply repr_div; [exact Ra | exact Rb | lra |].
    assert (Tb' : 0 <= IZR mz / 68719476736 <= 60000) by exact Tb.
    apply rnd_no_overflow_small. rewrite Rabs_right by lra.
    pose proof (bpow_le radix2 20 1000 ltac:(lia)) as H1. change (bpow radix2 20) with 1048576 in H1. lra.
  - change (Q2R (num # den)) with y. destruct (rnd_model t) as (eps & eta & Heps & Heta & _ & ->).
    pose proof eta_max_le_u. rewrite u_val in *.
    assert (Ht : Rabs (t - y) <= / 68719476736).
    { unfold t. apply Rabs_le. split.
      - apply (Rmult_le_reg_r 68719476736); [lra|]. field_simplify. lra.
      - apply (Rmult_le_reg_r 68719476736); [lra|]. field_simplify. lra. }
    replace (t * (1 + eps) + eta - y) with ((t - y) + t * eps + eta) by ring.
    eapply Rle_trans; [apply Rabs_triang|]. eapply Rle_trans; [apply Rplus_le_compat_r; apply Rabs_triang|].
    rewrite Rabs_mult. rewrite (Rabs_right t) by lra.
    assert (t * Rabs eps <= 60000 * (/ 4503599627370496 / 2)).
    { apply Rmult_le_compat; try lra. apply Rabs_pos. }
    lra.
Qed.
End P_FL.

(* ================================================================== *)
Section P_MS3.
Open Scope uint63_scope.

Lemma guard_true : forall E RR : int, (1 <= to_Z E + to_Z RR)%Z -> (to_Z E <= 2048)%Z -> (to_Z RR <= 2048)%Z ->
  ((to_Z E + to_Z RR) * (2 * to_Z E + to_Z RR + 1) <= 4194303)%Z -> guard E RR = true.
Proof.
  intros E RR H1 H2 H3 H4. unfold guard.
  pose proof (to_Z_bounded E). pose proof (to_Z_bounded RR).
  assert (A : to_Z (E + RR) = (to_Z E + to_Z RR)%Z) by (rewrite add_spec; apply Z.mod_small; rewrite wB_val; lia).
  assert (B2 : to_Z (E + (E + RR) + 1) = (2 * to_Z E + to_Z RR + 1)%Z).
  { rewrite add_spec, add_spec, A. change (to_Z 1) with 1%Z.
    rewrite (Z.mod_small (to_Z E + (to_Z E + to_Z RR))) by (rewrite wB_val; lia).
    rewrite Z.mod_small; [lia | rewrite wB_val; lia]. }
  assert (C : to_Z ((E + RR) * (E + (E + RR) + 1)) = ((to_Z E + to_Z RR) * (2 * to_Z E + to_Z RR + 1))%Z).
  { rewrite mul_spec, A, B2. apply Z.mod_small. split; [apply Z.mul_nonneg_nonneg; lia|]. rewrite wB_val. lia. }
  repeat (apply andb_true_iff; split); apply Uint63.leb_spec;
    rewrite ?A, ?C; change (to_Z 1) with 1%Z; change (to_Z 2048) with 2048%Z;
    change (to_Z 4194303) with 4194303%Z; lia.
Qed.


Lemma qcost_spec : forall E w cnt neg, (to_Z E < to_Z w)%Z -> (to_Z w <= 4194303)%Z ->
  to_Z (PArray.length (qcost E w cnt neg)) = to_Z w /\
  forall j, (0 <= j < to_Z w)%Z -> Q2R (qcost E w cnt neg).[of_Z j] =
    if Z.ltb j (to_Z E) then (if neg then (- IZR (to_Z cnt.[of_Z j]))%R else IZR (to_Z cnt.[of_Z j])) else 0%R.
Proof.
  intros E w cnt neg HE Hw. unfold qcost. pose proof (to_Z_bounded E).
  pose (Iv := fun ez (c : array Q) => to_Z (PArray.length c) = to_Z w /\
     forall j, (0 <= j < to_Z w)%Z -> Q2R c.[of_Z j] =
       if Z.ltb j ez then (if neg then (- IZR (to_Z cnt.[of_Z j]))%R else IZR (to_Z cnt.[of_Z j])) else 0%R).
  assert (G : Iv (to_Z E) (forl 0 E (fun e c => c.[e <- inject_Z (if neg then (- zofi cnt.[e])%Z else zofi cnt.[e])])
                 (PArray.make w 0%Q))).
  { apply (for_invZ Iv); unfold Iv.
    - change (to_Z 0) with 0%Z. lia.
    - rewrite lmakeQ by exact Hw. split; [reflexivity|]. intros j Hj. rewrite gmakeQ, Q2R_0.
      change (to_Z 0) with 0%Z. destruct (Z.ltb_spec j 0); [lia | reflexivity].
    - intros e c He [Hc P]. change (to_Z 0) with 0%Z in He. split; [rewrite lsetQ; exact Hc|].
      intros j Hj. destruct (Z.eq_dec j (to_Z e)) as [Eq|Nq].
      + subst j. rewrite of_Z_to_Z, gssQ by lia. rewrite Q2R_inject, zofi_spec.
        destruct (Z.ltb_spec (to_Z e) (to_Z e + 1)); [|lia]. destruct neg; [apply opp_IZR | reflexivity].
      + rewrite gsoZQ by (rewrite to_Z_of_Z_small by (rewrite wB_val; lia); lia). rewrite P by exact Hj.
        destruct (Z.ltb_spec j (to_Z e)); destruct (Z.ltb_spec j (to_Z e + 1)); try reflexivity; lia. }
  exact G.
Qed.

Section Sem.
Variables (dist : list (list Z)) (rs rd rt qs qd : list N).
Variables (xdist : array (array sint)) (xrs xrd xrt xqs xqd : array uint).
Hypothesis Hv : valid_input dist rs rd rt qs qd.
Hypothesis Rd : repr xdist dist.
Hypothesis Rrs : repr xrs rs.
Hypothesis Rrd : repr xrd rd.
Hypothesis Rrt : repr xrt rt.
Hypothesis Rqs : repr xqs qs.
Hypothesis Rqd : repr xqd qd.

Local Notation n := (PArray.length xdist).
Local Notation nn := (len dist).
Local Notation W := (flatten (PArray.length xdist) xdist).
Local Notation D := (fst (fw (PArray.length xdist) W)).
Local Notation X := (snd (fw (PArray.length xdist) W)).
Local Notation I := (fst (fst (scan_roads (PArray.length xdist) W))).
Local Notation P := (snd (fst (scan_roads (PArray.length xdist) W))).
Local Notation E := (snd (scan_roads (PArray.length xdist) W)).
Local Notation RR := (PArray.length xrs).
Local Notation Et := (Z.to_nat (to_Z E)).
Local Notation Rt := (Z.to_nat (to_Z RR)).

Lemma RR_val : to_Z RR = Z.of_N (len rs).
Proof. exact (repr_uint_len xrs rs Rrs). Qed.

Lemma Rt_val : Rt = List.length rs.
Proof. rewrite RR_val. unfold len. lia. Qed.

Lemma Hg : guard E RR = true.
Proof.
  pose proof (E_le dist rs rd rt qs qd xdist Hv Rd) as HE. pose proof RR_val as HR.
  destruct (vi_r _ _ _ _ _ _ Hv) as [R1 R2].
  pose proof (to_Z_bounded E).
  apply guard_true; try lia.
  assert (0 <= (to_Z E + to_Z RR) * (2 * to_Z E + to_Z RR + 1) <= 1000 * 1901)%Z
    by (split; [apply Z.mul_nonneg_nonneg | apply Z.mul_le_mono_nonneg]; lia).
  lia.
Qed.

Definition pe (e : nat) : Z := to_Z P.[of_Z (Z.of_nat e)].
Definition rA (e : nat) : N := Z.to_N (pe e / to_Z n).
Definition rB (e : nat) : N := Z.to_N (pe e mod to_Z n).
Definition idx (a b : N) : nat := Z.to_nat (dN n I a b).
Definition uR (e : nat) : R := IZR (ue W P (Z.of_nat e)).

Lemma road_e : forall e, (e < Et)%nat ->
  road dist (rA e) (rB e) /\ ue W P (Z.of_nat e) = entry dist (rA e) (rB e) /\ idx (rA e) (rB e) = e.
Proof.
  intros e He. pose proof (n_val dist xdist Rd) as En. pose proof (n_bounds dist rs rd rt qs qd xdist Hv Rd) as Bn.
  destruct (scan_facts dist rs rd rt qs qd xdist Hv Rd) as (_ & _ & _ & _ & S2).
  destruct (S2 (Z.of_nat e) ltac:(lia)) as (B1 & B2 & B3). fold (pe e) in B1.
  assert (Ep : pe e = (Z.of_N (rA e) * to_Z n + Z.of_N (rB e))%Z).
  { unfold rA, rB. pose proof (Z.div_mod (pe e) (to_Z n) ltac:(lia)).
    pose proof (Z.mod_pos_bound (pe e) (to_Z n) ltac:(lia)). pose proof (Z.div_pos (pe e) (to_Z n) ltac:(lia) ltac:(lia)).
    rewrite !Z2N.id by lia. lia. }
  assert (HaN : (rA e < nn)%N).
  { unfold rA. assert (pe e / to_Z n < to_Z n)%Z by (apply Z.div_lt_upper_bound; lia).
    pose proof (Z.div_pos (pe e) (to_Z n) ltac:(lia) ltac:(lia)). lia. }
  assert (HbN : (rB e < nn)%N).
  { unfold rB. pose proof (Z.mod_pos_bound (pe e) (to_Z n) ltac:(lia)). lia. }
  assert (EP : P.[of_Z (Z.of_nat e)] = of_Z (Z.of_N (rA e) * to_Z n + Z.of_N (rB e))).
  { rewrite <- Ep. unfold pe. rewrite of_Z_to_Z. reflexivity. }
  rewrite EP in B2, B3.
  split; [apply (isroad_iff dist n W (W_spec dist rs rd rt qs qd xdist Hv Rd)); assumption|].
  split.
  - unfold ue. rewrite EP, B2. rewrite zofs_spec. apply (W_spec dist rs rd rt qs qd xdist Hv Rd); assumption.
  - unfold idx, dN. rewrite B3. lia.
Qed.

Lemma idx_road : forall a b, road dist a b ->
  (idx a b < Et)%nat /\ rA (idx a b) = a /\ rB (idx a b) = b.
Proof.
  intros a b R. pose proof R as (Ha & Hb & _).
  pose proof (n_val dist xdist Rd) as En. pose proof (n_bounds dist rs rd rt qs qd xdist Hv Rd) as Bn.
  destruct (scan_facts dist rs rd rt qs qd xdist Hv Rd) as (_ & _ & _ & S1 & _).
  pose proof (pos_lt dist xdist Rd a b Ha Hb) as Hp.
  destruct (S1 _ Hp) as [L1 L2].
  { apply (isroad_iff dist n W (W_spec dist rs rd rt qs qd xdist Hv Rd)); assumption. }
  assert (Ei : of_Z (Z.of_nat (idx a b)) = I.[of_Z (Z.of_N a * to_Z n + Z.of_N b)]).
  { unfold idx, dN. rewrite Z2Nat.id by (apply to_Z_bounded). apply of_Z_to_Z. }
  assert (Epe : pe (idx a b) = (Z.of_N a * to_Z n + Z.of_N b)%Z) by (unfold pe; rewrite Ei; exact L2).
  split; [unfold idx, dN; pose proof (to_Z_bounded (I.[of_Z (Z.of_N a * to_Z n + Z.of_N b)])); clear - L1 H; lia|].
  unfold rA, rB. rewrite Epe. assert (Ha' : (Z.of_N a < to_Z n)%Z) by (clear - Ha En; lia). assert (Hb' : (Z.of_N b < to_Z n)%Z) by (clear - Hb En; lia).
  clear - Ha' Hb' Bn. split.
  - rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
  - rewrite Z.add_comm, Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma uR_pos : forall e, (e < Et)%nat -> (1 <= uR e <= 1000)%R.
Proof.
  intros e He. destruct (road_e e He) as (R & Eu & _). unfold uR. rewrite Eu.
  pose proof (road_le dist rs rd rt qs qd Hv _ _ R). split; apply IZR_le; lia.
Qed.


Local Notation T0 := (build_T n E RR W D X I P xrs xrd xrt).
Local Notation t0 := (cell (build_T n E RR W D X I P xrs xrd xrt) (E + (E + RR) + 1)).
Local Notation mn := (Z.to_nat (to_Z (E + RR))).
Local Notation A0n := (Z.to_nat (to_Z (E + E))).
Local Notation Ck := (cnt_k n E D X I xrs xrd).
Local Notation bK := (b_k n D xrs xrd xrt).

Lemma A0n_val : A0n = (Et + Et)%nat.
Proof.
  pose proof (E_le dist rs rd rt qs qd xdist Hv Rd) as HE. pose proof (to_Z_bounded E).
  assert (to_Z (E + E) = to_Z E + to_Z E)%Z by (rewrite add_spec; apply Z.mod_small; rewrite wB_val; lia).
  lia.
Qed.

Lemma mn_eq : mn = (Et + Rt)%nat.
Proof. apply (mn_val E RR Hg). Qed.

Lemma cntsum_nonneg : forall cnt z, (forall e, (0 <= e < to_Z E)%Z -> (0 <= to_Z cnt.[of_Z e])%Z) ->
  (forall e, (e < Et)%nat -> (0 <= z e)%R) -> (0 <= cntsum E cnt z)%R.
Proof.
  intros cnt z Hc Hz. unfold cntsum. apply sumR_nonneg. intros e He. apply Rmult_le_pos; [|apply Hz; exact He].
  apply IZR_le. apply Hc. clear - He. lia.
Qed.

Lemma cntsum_le : forall cnt z z', (forall e, (0 <= e < to_Z E)%Z -> (0 <= to_Z cnt.[of_Z e])%Z) ->
  (forall e, (e < Et)%nat -> (z e <= z' e)%R) -> (cntsum E cnt z <= cntsum E cnt z')%R.
Proof.
  intros cnt z z' Hc Hz. unfold cntsum. apply sumR_le. intros e He. apply Rmult_le_compat_l; [|apply Hz; exact He].
  apply IZR_le. apply Hc. clear - He. lia.
Qed.

Lemma cntsum_ext : forall cnt z z', (forall e, (e < Et)%nat -> z e = z' e) -> cntsum E cnt z = cntsum E cnt z'.
Proof. intros cnt z z' H. unfold cntsum. apply sumR_ext. intros e He. rewrite H by exact He. reflexivity. Qed.

Lemma sumR_term : forall n0 f k, (forall j, (j < n0)%nat -> (0 <= f j)%R) -> (k < n0)%nat -> (f k <= sumR n0 f)%R.
Proof.
  induction n0; intros f k Hf Hk; [lia|]. simpl. destruct (Nat.eq_dec k n0) as [->|Nk].
  - pose proof (sumR_nonneg n0 f ltac:(intros; apply Hf; lia)). lra.
  - pose proof (IHn0 f k ltac:(intros; apply Hf; lia) ltac:(lia)). pose proof (Hf n0 ltac:(lia)). lra.
Qed.

(* a trip of the input: two cities with a unique shortest route *)
Definition TripOK (s d : int) : Prop :=
  (toN s < nn)%N /\ (toN d < nn)%N /\ unique_shortest_route dist (toN s) (toN d).

Lemma TripOK_intro : forall s d a b, toN s = a -> toN d = b -> (a < nn)%N -> (b < nn)%N ->
  unique_shortest_route dist a b -> TripOK s d.
Proof. intros s d a b Ea Eb Ha Hb U. subst a b. split; [exact Ha|]. split; [exact Hb | exact U]. Qed.

Lemma deliv_ok : forall k, (k < Rt)%nat ->
  TripOK xrs.[of_Z (Z.of_nat k)] xrd.[of_Z (Z.of_nat k)] /\
  toN xrs.[of_Z (Z.of_nat k)] = get_list_N rs (N.of_nat k) /\
  toN xrd.[of_Z (Z.of_nat k)] = get_list_N rd (N.of_nat k) /\
  Z.to_N (to_Z xrt.[of_Z (Z.of_nat k)]) = get_list_N rt (N.of_nat k).
Proof.
  intros k Hk. rewrite Rt_val in Hk.
  pose proof (vi_rd _ _ _ _ _ _ Hv) as Ld. pose proof (vi_rt _ _ _ _ _ _ Hv) as Lt. unfold len in Ld, Lt.
  assert (Es : toN xrs.[of_Z (Z.of_nat k)] = get_list_N rs (N.of_nat k)) by (apply repr_uint_nth; assumption).
  assert (Ed : toN xrd.[of_Z (Z.of_nat k)] = get_list_N rd (N.of_nat k)) by (apply repr_uint_nth; [assumption | lia]).
  assert (Et' : Z.to_N (to_Z xrt.[of_Z (Z.of_nat k)]) = get_list_N rt (N.of_nat k)) by (apply repr_uint_nth; [assumption | lia]).
  split; [|auto].
  destruct (vi_r_cities _ _ _ _ _ _ Hv (N.of_nat k) ltac:(unfold len; lia)) as [C1 C2].
  pose proof (vi_r_unique _ _ _ _ _ _ Hv (N.of_nat k) ltac:(unfold len; lia)) as U.
  eapply TripOK_intro; [exact Es | exact Ed | exact C1 | exact C2 | exact U].
Qed.

Lemma query_ok : forall j, (j < List.length qs)%nat ->
  TripOK xqs.[of_Z (Z.of_nat j)] xqd.[of_Z (Z.of_nat j)] /\
  toN xqs.[of_Z (Z.of_nat j)] = get_list_N qs (N.of_nat j) /\
  toN xqd.[of_Z (Z.of_nat j)] = get_list_N qd (N.of_nat j).
Proof.
  intros j Hj.
  pose proof (vi_qd _ _ _ _ _ _ Hv) as Ld. unfold len in Ld.
  assert (Es : toN xqs.[of_Z (Z.of_nat j)] = get_list_N qs (N.of_nat j)) by (apply repr_uint_nth; assumption).
  assert (Ed : toN xqd.[of_Z (Z.of_nat j)] = get_list_N qd (N.of_nat j)) by (apply repr_uint_nth; [assumption | lia]).
  split; [|auto].
  destruct (vi_q_cities _ _ _ _ _ _ Hv (N.of_nat j) ltac:(unfold len; lia)) as [C1 C2].
  pose proof (vi_q_unique _ _ _ _ _ _ Hv (N.of_nat j) ltac:(unfold len; lia)) as U.
  eapply TripOK_intro; [exact Es | exact Ed | exact C1 | exact C2 | exact U].
Qed.

Definition RC (s d : int) := route_cnt n E D X I s d.
Definition Dsd (s d : int) : Z := dN n D (toN s) (toN d).

Lemma trip_facts : forall s d, TripOK s d ->
  to_Z (PArray.length (RC s d)) = to_Z E /\
  (forall e, (0 <= e < to_Z E)%Z -> (0 <= to_Z (RC s d).[of_Z e] <= to_Z INF)%Z) /\
  exists p, shortest_route dist (toN s) (toN d) p /\ distance dist p = Dsd s d /\
    (forall p', shortest_route dist (toN s) (toN d) p' -> p' = p) /\
    forall z, cntsum E (RC s d) z = psumR (fun a b => z (idx a b)) p.
Proof.
  intros s d (Hs & Hd & U). apply (route_cnt_spec dist rs rd rt qs qd xdist Hv Rd s d Hs Hd U).
Qed.

Lemma Dsd_get : forall s d, TripOK s d -> to_Z D.[s * n + d] = Dsd s d.
Proof.
  intros s d (Hs & Hd & _). unfold Dsd, dN. pose proof (n_val dist xdist Rd) as En.
  pose proof (n_le dist rs rd rt qs qd xdist Hv Rd) as Hn.
  rewrite (get_idx n Hn); [reflexivity | |]; unfold toN in *; pose proof (to_Z_bounded s); pose proof (to_Z_bounded d);
    clear - Hs Hd En H H0; lia.
Qed.

Lemma bK_val : forall k, (k < Rt)%nat ->
  bK k = (Z.of_N (get_list_N rt (N.of_nat k)) - Dsd xrs.[of_Z (Z.of_nat k)] xrd.[of_Z (Z.of_nat k)])%Z.
Proof.
  intros k Hk. destruct (deliv_ok k Hk) as (T & _ & _ & Et').
  unfold b_k, bk. rewrite !zofi_spec. rewrite Dsd_get by exact T. rewrite <- Et'.
  rewrite Z2N.id; [reflexivity | apply to_Z_bounded].
Qed.

Lemma Ck_eq : forall k, Ck k = RC xrs.[of_Z (Z.of_nat k)] xrd.[of_Z (Z.of_nat k)].
Proof. reflexivity. Qed.


Lemma Ck_facts : forall k, (k < Rt)%nat ->
  forall e, (0 <= e < to_Z E)%Z -> (0 <= to_Z (Ck k).[of_Z e])%Z.
Proof.
  intros k Hk e He. rewrite Ck_eq. destruct (deliv_ok k Hk) as (T & _).
  destruct (trip_facts _ _ T) as (_ & B & _). apply B. exact He.
Qed.

Lemma uR_nonneg : forall e, (e < Et)%nat -> (0 <= uR e)%R.
Proof. intros e He. pose proof (uR_pos e He). lra. Qed.

Definition zext (x : nat -> R) (j : nat) : R :=
  if Nat.ltb j Et then x j else if Nat.ltb j (Et + Et) then (uR (j - Et)%nat - x (j - Et)%nat)%R else 0%R.

Lemma sg_abs : forall b c, (sg b * c = IZR (Z.abs b))%R <-> c = IZR b.
Proof.
  intros b c. unfold sg. destruct (Z.ltb_spec b 0).
  - rewrite Z.abs_neq by lia. rewrite opp_IZR. split; intros; lra.
  - rewrite Z.abs_eq by lia. split; intros; lra.
Qed.

Lemma feas_x : forall z, Feas mn Et t0 A0n z ->
  (forall e, (e < Et)%nat -> (0 <= z e <= uR e)%R) /\
  (forall k, (k < Rt)%nat -> cntsum E (Ck k) z = IZR (bK k)) /\
  (forall j, (j < Et + (Et + Rt))%nat -> (0 <= z j)%R).
Proof.
  intros z (S & Pz & Az). unfold Sol in S. rewrite mn_eq in S, Pz, Az. rewrite A0n_val in Az.
  split; [|split; [|exact Pz]].
  - intros e He. pose proof (S e ltac:(lia)) as Se.
    rewrite (lin_bound n E RR W D X I P xrs xrd xrt Hg e z He), (rhs_bound n E RR W D X I P xrs xrd xrt Hg e He) in Se.
    pose proof (Pz e ltac:(lia)). pose proof (Pz (Et + e)%nat ltac:(lia)). unfold uR. lra.
  - intros k Hk. pose proof (S (Et + k)%nat ltac:(lia)) as Sk.
    rewrite (lin_deliv n E RR W D X I P xrs xrd xrt Hg k z Hk), (rhs_deliv n E RR W D X I P xrs xrd xrt Hg k Hk) in Sk.
    rewrite (Az (Et + Et + k)%nat ltac:(lia) ltac:(lia)) in Sk. rewrite Rplus_0_r in Sk.
    apply sg_abs. exact Sk.
Qed.

Lemma cntsum_zext : forall cnt x, cntsum E cnt (zext x) = cntsum E cnt x.
Proof.
  intros cnt x. apply cntsum_ext. intros e He. unfold zext. destruct (Nat.ltb_spec e Et); [reflexivity | lia].
Qed.

Lemma x_feas : forall x, (forall e, (e < Et)%nat -> (0 <= x e <= uR e)%R) ->
  (forall k, (k < Rt)%nat -> cntsum E (Ck k) x = IZR (bK k)) ->
  Feas mn Et t0 A0n (zext x).
Proof.
  intros x Hx Hd. unfold Feas, Sol. rewrite mn_eq, A0n_val. split; [|split].
  - intros r Hr. destruct (Nat.ltb_spec r Et).
    + rewrite (lin_bound n E RR W D X I P xrs xrd xrt Hg r _ H), (rhs_bound n E RR W D X I P xrs xrd xrt Hg r H).
      unfold zext. destruct (Nat.ltb_spec r Et); [|lia]. destruct (Nat.ltb_spec (Et + r) Et); [lia|].
      destruct (Nat.ltb_spec (Et + r) (Et + Et)); [|lia]. replace (Et + r - Et)%nat with r by lia.
      unfold uR. ring.
    + replace r with (Et + (r - Et))%nat by lia.
      rewrite (lin_deliv n E RR W D X I P xrs xrd xrt Hg (r - Et) _ ltac:(lia)),
              (rhs_deliv n E RR W D X I P xrs xrd xrt Hg (r - Et) ltac:(lia)).
      rewrite cntsum_zext. rewrite Hd by lia.
      unfold zext. destruct (Nat.ltb_spec (Et + Et + (r - Et)) Et); [lia|].
      destruct (Nat.ltb_spec (Et + Et + (r - Et)) (Et + Et)); [lia|].
      rewrite Rplus_0_r. apply sg_abs. reflexivity.
  - intros j Hj. unfold zext. destruct (Nat.ltb_spec j Et); [apply Hx; exact H|].
    destruct (Nat.ltb_spec j (Et + Et)); [|lra]. pose proof (Hx (j - Et)%nat ltac:(lia)). lra.
  - intros j Hj1 Hj2. unfold zext. destruct (Nat.ltb_spec j Et); [lia|].
    destruct (Nat.ltb_spec j (Et + Et)); [lia | reflexivity].
Qed.

Definition Mb : R :=
  (sumR Et uR + sumR Rt (fun k => IZR (Z.abs (bK k)) + cntsum E (Ck k) uR))%R.

Lemma bounded : Bounded mn Et t0 Mb.
Proof.
  intros z S Pz j Hj. rewrite mn_eq in Hj, Pz. unfold Sol in S. rewrite mn_eq in S.
  assert (Bu : forall e, (e < Et)%nat -> (z e <= uR e)%R).
  { intros e He. pose proof (S e ltac:(lia)) as Se.
    rewrite (lin_bound n E RR W D X I P xrs xrd xrt Hg e z He), (rhs_bound n E RR W D X I P xrs xrd xrt Hg e He) in Se.
    pose proof (Pz (Et + e)%nat ltac:(lia)). unfold uR. lra. }
  assert (Pk : forall k, (k < Rt)%nat -> (0 <= IZR (Z.abs (bK k)) + cntsum E (Ck k) uR)%R).
  { intros k Hk. pose proof (IZR_le 0 _ (Z.abs_nonneg (bK k))).
    pose proof (cntsum_nonneg (Ck k) uR (Ck_facts k Hk) uR_nonneg). lra. }
  assert (S1 : (0 <= sumR Et uR)%R) by (apply sumR_nonneg; exact uR_nonneg).
  assert (S2 : (0 <= sumR Rt (fun k => IZR (Z.abs (bK k)) + cntsum E (Ck k) uR))%R) by (apply sumR_nonneg; exact Pk).
  unfold Mb.
  destruct (Nat.ltb_spec j Et).
  - pose proof (Bu j H). pose proof (sumR_term Et uR j uR_nonneg H). lra.
  - destruct (Nat.ltb_spec j (Et + Et)).
    + pose proof (S (j - Et)%nat ltac:(lia)) as Se.
      rewrite (lin_bound n E RR W D X I P xrs xrd xrt Hg (j - Et) z ltac:(lia)),
              (rhs_bound n E RR W D X I P xrs xrd xrt Hg (j - Et) ltac:(lia)) in Se.
      replace (Et + (j - Et))%nat with j in Se by lia.
      pose proof (Pz (j - Et)%nat ltac:(lia)). pose proof (sumR_term Et uR (j - Et) uR_nonneg ltac:(lia)).
      unfold uR in *. lra.
    + set (k := (j - Et - Et)%nat). assert (Hk : (k < Rt)%nat) by (unfold k; lia).
      pose proof (S (Et + k)%nat ltac:(lia)) as Sk.
      rewrite (lin_deliv n E RR W D X I P xrs xrd xrt Hg k z Hk), (rhs_deliv n E RR W D X I P xrs xrd xrt Hg k Hk) in Sk.
      replace (Et + Et + k)%nat with j in Sk by (unfold k; lia).
      pose proof (cntsum_nonneg (Ck k) z (Ck_facts k Hk) (fun e He => Pz e ltac:(lia))) as C0.
      pose proof (cntsum_le (Ck k) z uR (Ck_facts k Hk) Bu) as C1.
      pose proof (sumR_term Rt _ k Pk Hk) as T. cbv beta in T.
      assert (Hs : (- cntsum E (Ck k) z <= sg (bK k) * cntsum E (Ck k) z)%R).
      { unfold sg. destruct (Z.ltb (bK k) 0); lra. }
      lra.
Qed.

Definition xv (v : N -> N -> R) (e : nat) : R := (60 * uR e / v (rA e) (rB e) - uR e)%R.
Definition vx (x : nat -> R) (a b : N) : R :=
  (60 * IZR (entry dist a b) / (IZR (entry dist a b) + x (idx a b)))%R.

Lemma xv_rel : forall v, forall a b, road dist a b ->
  (60 * IZR (entry dist a b) / v a b = IZR (entry dist a b) + xv v (idx a b))%R.
Proof.
  intros v a b R. destruct (idx_road a b R) as (Hi & Ea & Eb). destruct (road_e _ Hi) as (_ & Eu & _).
  unfold xv, uR. rewrite Eu, Ea, Eb. ring.
Qed.

Lemma xv_bounds : forall v, speeds_ok dist v -> forall e, (e < Et)%nat -> (0 <= xv v e <= uR e)%R.
Proof.
  intros v Hs e He. destruct (road_e e He) as (R & _ & _). pose proof (Hs _ _ R) as Hv'.
  pose proof (uR_pos e He). unfold xv. set (u := uR e) in *. set (vv := v (rA e) (rB e)) in *.
  assert (A : (60 * u / vv = u * (60 / vv))%R) by (field; lra). rewrite A.
  assert (B1 : (1 <= 60 / vv)%R) by (apply (Rmult_le_reg_r vv); [lra|]; field_simplify; lra).
  assert (B2 : (60 / vv <= 2)%R) by (apply (Rmult_le_reg_r vv); [lra|]; field_simplify; lra).
  split; nra.
Qed.

Lemma vx_rel : forall x, (forall e, (e < Et)%nat -> (0 <= x e <= uR e)%R) ->
  forall a b, road dist a b ->
  (60 * IZR (entry dist a b) / vx x a b = IZR (entry dist a b) + x (idx a b))%R.
Proof.
  intros x Hx a b R. destruct (idx_road a b R) as (Hi & _ & _). pose proof (Hx _ Hi).
  pose proof (road_le dist rs rd rt qs qd Hv _ _ R) as Re. pose proof (IZR_le 1 _ (proj1 Re)).
  unfold vx. field. lra.
Qed.

Lemma vx_speeds : forall x, (forall e, (e < Et)%nat -> (0 <= x e <= uR e)%R) -> speeds_ok dist (vx x).
Proof.
  intros x Hx a b R. destruct (idx_road a b R) as (Hi & Ea & Eb). pose proof (Hx _ Hi) as Bx.
  destruct (road_e _ Hi) as (_ & Eu & _). unfold uR in Bx. rewrite Eu, Ea, Eb in Bx.
  pose proof (road_le dist rs rd rt qs qd Hv _ _ R) as Re. pose proof (IZR_le 1 _ (proj1 Re)).
  unfold vx. set (e := IZR (entry dist a b)) in *. set (y := x (idx a b)) in *.
  split.
  - apply (Rmult_le_reg_r (e + y)); [lra|]. field_simplify; lra.
  - apply (Rmult_le_reg_r (e + y)); [lra|]. field_simplify; lra.
Qed.

Lemma trip_dur : forall s d, TripOK s d -> forall (v : N -> N -> R) (x : nat -> R),
  (forall a b, road dist a b -> (60 * IZR (entry dist a b) / v a b = IZR (entry dist a b) + x (idx a b))%R) ->
  forall t, trip_takes dist v (toN s) (toN d) t <-> t = (IZR (Dsd s d) + cntsum E (RC s d) x)%R.
Proof.
  intros s d T v x Hr t. destruct (trip_facts s d T) as (_ & _ & p & Sh & Dp & Un & Cs).
  pose proof (dur_gen dist v (fun a b => x (idx a b)) Hr _ _ _ (proj1 Sh)) as Du.
  rewrite Cs, <- Dp. split.
  - intros H. rewrite <- (H p Sh). exact Du.
  - intros -> p' Sh'. rewrite (Un p' Sh'). exact Du.
Qed.

Lemma deliv_iff : forall (v : N -> N -> R) (x : nat -> R),
  (forall a b, road dist a b -> (60 * IZR (entry dist a b) / v a b = IZR (entry dist a b) + x (idx a b))%R) ->
  matches_deliveries dist rs rd rt v <-> forall k, (k < Rt)%nat -> cntsum E (Ck k) x = IZR (bK k).
Proof.
  intros v x Hr. unfold matches_deliveries. split.
  - intros H k Hk. destruct (deliv_ok k Hk) as (T & Es & Ed & Et').
    pose proof (H (N.of_nat k) ltac:(rewrite Rt_val in Hk; unfold len; lia)) as Hk'.
    rewrite <- Es, <- Ed in Hk'. apply (trip_dur _ _ T v x Hr) in Hk'.
    rewrite Ck_eq, bK_val by exact Hk. rewrite minus_IZR. lra.
  - intros H k Hk. set (kn := N.to_nat k). assert (Ek : k = N.of_nat kn) by (unfold kn; lia).
    assert (Hkn : (kn < Rt)%nat) by (rewrite Rt_val; unfold len in Hk; lia).
    destruct (deliv_ok kn Hkn) as (T & Es & Ed & Et'). rewrite Ek, <- Es, <- Ed.
    apply (trip_dur _ _ T v x Hr). pose proof (H kn Hkn) as Hc. rewrite Ck_eq, bK_val in Hc by exact Hkn.
    rewrite minus_IZR in Hc. lra.
Qed.

Lemma possible_iff : forall s d, TripOK s d -> forall t,
  possible dist rs rd rt (toN s) (toN d) t <->
  exists x, (forall e, (e < Et)%nat -> (0 <= x e <= uR e)%R) /\
    (forall k, (k < Rt)%nat -> cntsum E (Ck k) x = IZR (bK k)) /\
    t = (IZR (Dsd s d) + cntsum E (RC s d) x)%R.
Proof.
  intros s d T t. split.
  - intros (v & Hs & Hm & Ht). exists (xv v). split; [apply xv_bounds; exact Hs|].
    split; [apply (deliv_iff v (xv v) (xv_rel v)); exact Hm|].
    apply (trip_dur _ _ T v (xv v) (xv_rel v)). exact Ht.
  - intros (x & Hb & Hd & Ht). exists (vx x). split; [apply vx_speeds; exact Hb|].
    split; [apply (deliv_iff (vx x) x (vx_rel x Hb)); exact Hd|].
    apply (trip_dur _ _ T (vx x) x (vx_rel x Hb)). exact Ht.
Qed.

Lemma feas_exists : exists x0, Feas mn Et t0 A0n x0.
Proof.
  destruct (vi_consistent _ _ _ _ _ _ Hv) as (v & Hs & Hm).
  exists (zext (xv v)). apply x_feas; [apply xv_bounds; exact Hs|].
  apply (deliv_iff v (xv v) (xv_rel v)). exact Hm.
Qed.


Local Notation w := (E + (E + RR) + 1).
Local Notation NN := (E + (E + RR)).

Lemma w_facts : (to_Z E < to_Z w)%Z /\ (to_Z w <= 4194303)%Z /\ to_Z w = (2 * to_Z E + to_Z RR + 1)%Z.
Proof.
  pose proof (w_val' E RR Hg) as Ew. pose proof (E_le dist rs rd rt qs qd xdist Hv Rd).
  pose proof RR_val. destruct (vi_r _ _ _ _ _ _ Hv). pose proof (to_Z_bounded RR). lia.
Qed.

Lemma cost_eq : forall cnt neg z,
  sumR (Et + mn) (fun j => (ovec (qcost E w cnt neg) j * z j)%R) =
  (if neg then - cntsum E cnt z else cntsum E cnt z)%R.
Proof.
  intros cnt neg z. destruct w_facts as (W1 & W2 & W3).
  destruct (qcost_spec E w cnt neg W1 W2) as [_ Pc].
  rewrite mn_eq. rewrite sumR_split.
  rewrite (sumR_zero (Et + Rt)).
  2:{ intros i Hi. unfold ovec. rewrite Pc by (pose proof (to_Z_bounded E); pose proof RR_val; clear - Hi W3 H H0; lia).
      destruct (Z.ltb_spec (Z.of_nat (Et + i)) (to_Z E)); [lia | ring]. }
  rewrite Rplus_0_r. unfold cntsum.
  assert (Ex : forall j, (j < Et)%nat -> (ovec (qcost E w cnt neg) j * z j =
      (if neg then -1 else 1) * (IZR (to_Z cnt.[of_Z (Z.of_nat j)]) * z j))%R).
  { intros j Hj. unfold ovec. rewrite Pc by (pose proof (to_Z_bounded E); clear - Hj W1; lia).
    destruct (Z.ltb_spec (Z.of_nat j) (to_Z E)); [|lia]. destruct neg; ring. }
  rewrite (sumR_ext _ _ _ Ex), sumR_scal. destruct neg; ring.
Qed.

Lemma carr_N : forall cnt neg, Q2R (qcost E w cnt neg).[NN] = 0%R.
Proof.
  intros cnt neg. destruct w_facts as (W1 & W2 & W3). destruct (qcost_spec E w cnt neg W1 W2) as [_ Pc].
  pose proof (N_val' E RR Hg) as EN.
  pose proof (Pc (to_Z NN) ltac:(pose proof (to_Z_bounded NN); lia)) as H. rewrite of_Z_to_Z in H. rewrite H.
  destruct (Z.ltb_spec (to_Z NN) (to_Z E)); [|reflexivity].
  pose proof (to_Z_bounded RR). lia.
Qed.

Lemma carr_len : forall cnt neg, to_Z (PArray.length (qcost E w cnt neg)) = to_Z w.
Proof. intros cnt neg. destruct w_facts as (W1 & W2 & _). apply (qcost_spec E w cnt neg W1 W2). Qed.

Lemma psum_u : forall s d p, route dist s d p ->
  psumR (fun a b => uR (idx a b)) p = IZR (distance dist p).
Proof.
  intros s d p R. induction R as [s Hs | s m d p Rr Rp IH].
  - simpl. reflexivity.
  - destruct (route_head dist _ _ _ Rp) as [tl ->]. rewrite distance_cons2. simpl psumR.
    simpl psumR in IH. rewrite IH. destruct (idx_road _ _ Rr) as (Hi & Ea & Eb).
    destruct (road_e _ Hi) as (_ & Eu & _). unfold uR. rewrite Eu, Ea, Eb. rewrite plus_IZR. reflexivity.
Qed.

Section Q.
Variable Hp : P1ok T0 (E + RR) E (E + E).

Local Notation st1 := (phase1 T0 (E + RR) E (E + E) Hp).
Local Notation Hv1 := (phase1_VS T0 (E + RR) E (E + E) Hp).
Local Notation al := (al2 (sO (phase1 T0 (E + RR) E (E + E) Hp)) (E + E) NN).
Local Notation VQ := (vq n E RR D X I T0 Hp st1 Hv1 al).

Lemma vq_spec : forall (s d : int) (neg : bool),
  (exists z, Feas mn Et t0 A0n z /\
     (if neg then - cntsum E (RC s d) z else cntsum E (RC s d) z)%R = Q2R (VQ s d neg)) /\
  (forall z, Feas mn Et t0 A0n z ->
     (Q2R (VQ s d neg) <= if neg then - cntsum E (RC s d) z else cntsum E (RC s d) z)%R).
Proof.
  intros s d neg.
  assert (HA0 : (to_Z (E + E) <= to_Z E + to_Z (E + RR))%Z).
  { pose proof A0n_val. pose proof mn_eq. pose proof (to_Z_bounded (E + E)). pose proof (to_Z_bounded (E + RR)). lia. }
  pose proof (phase2_min T0 (E + RR) E (E + E) Hp HA0 Mb bounded feas_exists
                (qcost E w (route_cnt n E D X I s d) neg) (carr_len _ _) (carr_N _ _)) as G.
  cbv zeta in G. unfold p1st in G.
  destruct G as [[z [Fz Cz]] Lz]. split.
  - exists z. split; [exact Fz|]. rewrite <- cost_eq. exact Cz.
  - intros z' Fz'. rewrite <- cost_eq. exact (Lz z' Fz').
Qed.

Lemma query_sem : forall s d, TripOK s d ->
  least_possible dist rs rd rt (toN s) (toN d) (IZR (Dsd s d) + Q2R (VQ s d false))%R /\
  greatest_possible dist rs rd rt (toN s) (toN d) (IZR (Dsd s d) - Q2R (VQ s d true))%R /\
  (0 <= IZR (Dsd s d) + Q2R (VQ s d false))%R /\
  (IZR (Dsd s d) - Q2R (VQ s d true) <= 60000)%R /\
  (IZR (Dsd s d) + Q2R (VQ s d false) <= IZR (Dsd s d) - Q2R (VQ s d true))%R.
Proof.
  intros s d T.
  destruct (trip_facts s d T) as (_ & Cb & p & Sh & Dp & _ & Cs).
  destruct (vq_spec s d false) as [[z1 [F1 C1]] L1]. destruct (vq_spec s d true) as [[z2 [F2 C2]] L2].
  destruct (feas_x z1 F1) as (B1 & D1 & P1). destruct (feas_x z2 F2) as (B2 & D2 & P2).
  assert (Cn : forall z, (forall e, (e < Et)%nat -> (0 <= z e)%R) -> (0 <= cntsum E (RC s d) z)%R).
  { intros z Hz. apply cntsum_nonneg; [|exact Hz]. intros e He. apply Cb. exact He. }
  assert (Cu : forall z, (forall e, (e < Et)%nat -> (0 <= z e <= uR e)%R) ->
            (cntsum E (RC s d) z <= IZR (Dsd s d))%R).
  { intros z Hz. rewrite <- Dp. rewrite <- (psum_u _ _ _ (proj1 Sh)). rewrite <- Cs.
    apply cntsum_le; [intros e He; apply Cb; exact He|]. intros e He. apply Hz. exact He. }
  assert (Dn : (0 <= IZR (Dsd s d))%R).
  { rewrite <- Dp. apply IZR_le. apply (distance_nonneg dist _ _ _ (proj1 Sh)). }
  assert (Db : (IZR (Dsd s d) <= 29000)%R).
  { rewrite <- Dp. apply IZR_le. pose proof (shortest_bound dist rs rd rt qs qd Hv _ _ _ Sh).
    destruct (vi_n _ _ _ _ _ _ Hv). lia. }
  assert (Ex1 : possible dist rs rd rt (toN s) (toN d) (IZR (Dsd s d) + Q2R (VQ s d false))%R).
  { apply (possible_iff s d T). exists z1. split; [exact B1|]. split; [exact D1|]. rewrite <- C1. reflexivity. }
  assert (Ex2 : possible dist rs rd rt (toN s) (toN d) (IZR (Dsd s d) - Q2R (VQ s d true))%R).
  { apply (possible_iff s d T). exists z2. split; [exact B2|]. split; [exact D2|]. rewrite <- C2. ring. }
  split.
  { split; [exact Ex1|]. intros t' Ht'. apply (possible_iff s d T) in Ht'. destruct Ht' as (x & Bx & Dx & ->).
    pose proof (L1 (zext x) (x_feas x Bx Dx)) as L. rewrite cntsum_zext in L. lra. }
  split.
  { split; [exact Ex2|]. intros t' Ht'. apply (possible_iff s d T) in Ht'. destruct Ht' as (x & Bx & Dx & ->).
    pose proof (L2 (zext x) (x_feas x Bx Dx)) as L. rewrite cntsum_zext in L. lra. }
  pose proof (Cn z1 (fun e He => proj1 (B1 e He))). pose proof (Cu z2 B2). pose proof (L1 z2 F2).
  rewrite <- C1, <- C2. split; [lra|]. split; lra.
Qed.

Lemma dq_R : forall s d, TripOK s d -> Q2R (dq n D s d) = IZR (Dsd s d).
Proof.
  intros s d T. unfold dq. rewrite Q2R_inject, zofi_spec. exact (f_equal IZR (Dsd_get s d T)).
Qed.

Local Notation QA := (qans n E RR D X I T0 Hp st1 Hv1 al).

Lemma qans_spec : forall s d, TripOK s d ->
  exists lo hi, least_possible dist rs rd rt (toN s) (toN d) lo /\
    greatest_possible dist rs rd rt (toN s) (toN d) hi /\
    repr (fst (QA s d)) (fval (fst (QA s d))) /\ repr (snd (QA s d)) (fval (snd (QA s d))) /\
    close (fval (fst (QA s d))) lo /\ close (fval (snd (QA s d))) hi.
Proof.
  intros s d T. destruct (query_sem s d T) as (Hl & Hh & B1 & B2 & B3).
  exists (IZR (Dsd s d) + Q2R (VQ s d false))%R, (IZR (Dsd s d) - Q2R (VQ s d true))%R.
  split; [exact Hl|]. split; [exact Hh|].
  assert (E1 : Q2R (Qplus (dq n D s d) (VQ s d false)) = (IZR (Dsd s d) + Q2R (VQ s d false))%R)
    by (rewrite Q2R_plus, dq_R by exact T; reflexivity).
  assert (E2 : Q2R (Qminus (dq n D s d) (VQ s d true)) = (IZR (Dsd s d) - Q2R (VQ s d true))%R)
    by (rewrite Q2R_minus, dq_R by exact T; reflexivity).
  destruct (q2f_spec (Qplus (dq n D s d) (VQ s d false)) ltac:(rewrite E1; lra)) as (r1 & R1 & L1).
  destruct (q2f_spec (Qminus (dq n D s d) (VQ s d true)) ltac:(rewrite E2; lra)) as (r2 & R2 & L2).
  unfold qans. simpl fst. simpl snd.
  assert (F1 : fval (q2f (Qplus (dq n D s d) (VQ s d false))) = r1) by (destruct R1; assumption).
  assert (F2 : fval (q2f (Qminus (dq n D s d) (VQ s d true))) = r2) by (destruct R2; assumption).
  rewrite F1, F2. split; [exact R1|]. split; [exact R2|].
  rewrite E1 in L1. rewrite E2 in L2. split; left; assumption.
Qed.

End Q.

End Sem.
End P_MS3.

(* ================================================================== *)
Section P_MF.
Open Scope uint63_scope.

Lemma lboundP : forall (t : array (float * float)), (to_Z (PArray.length t) <= 4194303)%Z.
Proof. intros t. pose proof (leb_length (float * float) t) as H. rewrite Uint63.leb_spec in H. exact H. Qed.

Lemma fill1P : forall (nq : int) (f : int -> array (float * float) -> array (float * float))
    (F : int -> float * float) (z0 : float * float),
  (forall j out, f j out = out.[j <- F j]) -> (to_Z nq <= 4194303)%Z ->
  PArray.length (forl 0 nq f (PArray.make nq z0)) = nq /\
  forall j, (to_Z j < to_Z nq)%Z -> (forl 0 nq f (PArray.make nq z0)).[j] = F j.
Proof.
  intros nq f F z0 Hf Hn.
  pose (Iv := fun kz (out : array (float * float)) => PArray.length out = nq /\
     forall j, (to_Z j < kz)%Z -> out.[j] = F j).
  assert (G : Iv (to_Z nq) (forl 0 nq f (PArray.make nq z0))).
  { apply (for_invZ Iv); unfold Iv.
    - change (to_Z 0) with 0%Z. pose proof (to_Z_bounded nq). lia.
    - split.
      + etransitivity; [exact (length_make _ nq z0)|]. replace (nq <=? max_length) with true; [reflexivity|].
        symmetry. rewrite Uint63.leb_spec. exact Hn.
      + intros j Hj. change (to_Z 0) with 0%Z in Hj. pose proof (to_Z_bounded j). lia.
    - intros j out Hj [HL P]. change (to_Z 0) with 0%Z in Hj. rewrite Hf. split.
      + etransitivity; [exact (length_set _ out j (F j)) | exact HL].
      + intros j' Hj'. destruct (Z.eq_dec (to_Z j') (to_Z j)) as [E|E].
        * apply to_Z_inj in E. subst j'. assert (Hlt : (j <? PArray.length out) = true) by (rewrite Uint63.ltb_spec, HL; lia).
          exact (get_set_same _ out j (F j) Hlt).
        * assert (Nj : j <> j') by (intros F'; apply E; rewrite F'; reflexivity).
          etransitivity; [exact (get_set_other _ out j j' (F j) Nj) | apply P; lia]. }
  exact G.
Qed.

Section Main.
Variables (dist : list (list Z)) (rs rd rt qs qd : list N).
Variables (xdist : array (array sint)) (xrs xrd xrt xqs xqd : array uint).
Hypothesis Hv : valid_input dist rs rd rt qs qd.
Hypothesis Rd : repr xdist dist.
Hypothesis Rrs : repr xrs rs.
Hypothesis Rrd : repr xrd rd.
Hypothesis Rrt : repr xrt rt.
Hypothesis Rqs : repr xqs qs.
Hypothesis Rqd : repr xqd qd.

Local Notation n := (PArray.length xdist).
Local Notation W := (flatten (PArray.length xdist) xdist).
Local Notation D := (fst (fw (PArray.length xdist) W)).
Local Notation X := (snd (fw (PArray.length xdist) W)).
Local Notation I := (fst (fst (scan_roads (PArray.length xdist) W))).
Local Notation P := (snd (fst (scan_roads (PArray.length xdist) W))).
Local Notation E := (snd (scan_roads (PArray.length xdist) W)).
Local Notation RR := (PArray.length xrs).
Local Notation T0 := (build_T n E RR W D X I P xrs xrd xrt).
Local Notation NN := (E + (E + RR)).

Lemma nq_val : to_Z (PArray.length xqs) = Z.of_nat (List.length qs).
Proof. pose proof (repr_uint_len xqs qs Rqs) as H. unfold len in H. etransitivity; [exact H | lia]. Qed.

Theorem main_correct : exists o : list (R * R),
  repr (roadtimes_impl xdist xrs xrd xrt xqs xqd) o /\ roadtimes_spec dist rs rd rt qs qd o.
Proof.
  unfold roadtimes_impl. cbv zeta.
  destruct (bdec (guard E RR)) as [Hg'|Hg'].
  2:{ exfalso. rewrite (Hg dist rs rd rt qs qd xdist xrs Hv Rd Rrs) in Hg'. discriminate. }
  unfold answers. cbv zeta.
  pose (Hp := build_ok n E RR W D X I P xrs xrd xrt Hg').
  pose (F := fun j => qans n E RR D X I T0 Hp (phase1 T0 (E + RR) E (E + E) Hp)
                       (phase1_VS T0 (E + RR) E (E + E) Hp) (al2 (sO (phase1 T0 (E + RR) E (E + E) Hp)) (E + E) NN)
                       (aget xqs j) (aget xqd j)).
  match goal with |- context [forl 0 ?nq ?f (PArray.make ?nq ?z0)] => set (ff := f) end.
  assert (Hf : forall j out, ff j out = out.[j <- F j]) by (intros j out; exact_no_check (eq_refl (ff j out))).
  destruct (fill1P (PArray.length xqs) ff F (PrimFloat.zero, PrimFloat.zero) Hf (lboundI xqs)) as [HL' HC'].
  set (out := forl 0 (PArray.length xqs) ff (PArray.make (PArray.length xqs) (PrimFloat.zero, PrimFloat.zero))) in *.
  pose (o := map (fun k => (fval (fst (F (of_Z (Z.of_nat k)))), fval (snd (F (of_Z (Z.of_nat k))))))
                 (seq 0 (List.length qs))).
  assert (Lo : List.length o = List.length qs) by (unfold o; rewrite length_map, length_seq; reflexivity).
  assert (No : forall k, (k < List.length qs)%nat ->
            nth_error o k = Some (fval (fst (F (of_Z (Z.of_nat k)))), fval (snd (F (of_Z (Z.of_nat k)))))).
  { intros k Hk. unfold o. rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec k (List.length qs)); [reflexivity|lia]. }
  assert (Qk : forall k, (k < List.length qs)%nat ->
     exists lo hi, least_possible dist rs rd rt (get_list_N qs (N.of_nat k)) (get_list_N qd (N.of_nat k)) lo /\
       greatest_possible dist rs rd rt (get_list_N qs (N.of_nat k)) (get_list_N qd (N.of_nat k)) hi /\
       repr (fst (F (of_Z (Z.of_nat k)))) (fval (fst (F (of_Z (Z.of_nat k))))) /\
       repr (snd (F (of_Z (Z.of_nat k)))) (fval (snd (F (of_Z (Z.of_nat k))))) /\
       close (fval (fst (F (of_Z (Z.of_nat k))))) lo /\ close (fval (snd (F (of_Z (Z.of_nat k))))) hi).
  { intros k Hk. destruct (query_ok dist rs rd rt qs qd xqs xqd Hv Rqs Rqd k Hk) as (T & Es & Ed).
    assert (T' : TripOK dist (aget xqs (of_Z (Z.of_nat k))) (aget xqd (of_Z (Z.of_nat k)))) by exact T.
    assert (Es' : toN (aget xqs (of_Z (Z.of_nat k))) = get_list_N qs (N.of_nat k)) by exact Es.
    assert (Ed' : toN (aget xqd (of_Z (Z.of_nat k))) = get_list_N qd (N.of_nat k)) by exact Ed.
    destruct (qans_spec dist rs rd rt qs qd xdist xrs xrd xrt Hv Rd Rrs Rrd Rrt Hp _ _ T')
      as (lo & hi & H1 & H2 & H3 & H4 & H5 & H6).
    rewrite Es', Ed' in H1, H2.
    exists lo, hi. exact_no_check (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 H6))))). }
  exists o. split.
  - split.
    + rewrite Lo. rewrite <- nq_val. exact_no_check (f_equal to_Z (eq_sym HL')).
    + intros k Hk. rewrite Lo in Hk. eexists. split; [apply No; exact Hk|].
      destruct (Qk k Hk) as (lo & hi & _ & _ & R1 & R2 & _).
      assert (Hk' : (to_Z (of_Z (Z.of_nat k)) < to_Z (PArray.length xqs))%Z).
      { pose proof nq_val. rewrite to_Z_of_Z_small by (rewrite wB_val; pose proof (lboundI xqs); lia). lia. }
      pose proof (HC' _ Hk') as Ek.
      assert (Rp : repr (F (of_Z (Z.of_nat k)))
                        (fval (fst (F (of_Z (Z.of_nat k)))), fval (snd (F (of_Z (Z.of_nat k)))))) by (split; assumption).
      exact_no_check (eq_ind_r (fun c => repr c (fval (fst (F (of_Z (Z.of_nat k)))), fval (snd (F (of_Z (Z.of_nat k)))))) Rp Ek).
  - split.
    + unfold len. rewrite Lo. reflexivity.
    + intros j Hj. unfold len in Hj. set (k := N.to_nat j).
      assert (Hk : (k < List.length qs)%nat) by (unfold k; lia).
      destruct (Qk k Hk) as (lo & hi & H1 & H2 & _ & _ & H5 & H6).
      replace (N.of_nat k) with j in H1, H2 by (unfold k; lia).
      exists lo, hi. split; [exact H1|]. split; [exact H2|].
      rewrite (nth_error_nth o k (0%R, 0%R) (No k Hk)). simpl fst; simpl snd. split; assumption.
Qed.

End Main.
End P_MF.

Definition roadtimes_correct :
  forall (dist : list (list Z)) (rs rd rt qs qd : list N)
         (xdist : array (array sint))
         (xrs xrd xrt xqs xqd : array uint),
    valid_input dist rs rd rt qs qd ->
    repr xdist dist -> repr xrs rs -> repr xrd rd -> repr xrt rt ->
    repr xqs qs -> repr xqd qd ->
    exists o : list (R * R),
      repr (roadtimes xdist xrs xrd xrt xqs xqd) o /\
      roadtimes_spec dist rs rd rt qs qd o
  := main_correct.
