(* Correctness proofs for mazemovement_implem.v. *)
(* Implementation of mazemovement (mazemovement.spec): push-relabel
   maximum flow, first phase, on the dense n x n residual table.
   See README.md, section Implementation, for the design and the proof. *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Bool Uint63 PArray ZifyUint63 Lia Zwf.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.
Open Scope bool_scope.

Unset Lia Cache.

Require Export mazemovement_implem.
Open Scope uint63_scope.
Open Scope array_scope.
Open Scope bool_scope.


Lemma int_neq : forall a b : int, (φ a) <> (φ b) -> a <> b.
Proof. intros a b H E. apply H. rewrite E. reflexivity. Qed.

Ltac bcase e := let E := fresh "E" in destruct e eqn:E; bnorm.

Lemma rng_ok_complete : forall x n (z : Z) i H, gap n i = z ->
  (forall j, ((φ i) <= (φ j) < (φ n))%Z -> (2 <= (φ (x.[j])) <= 2000000000)%Z) ->
  rng_ok x n i H = true.
Proof.
  intros x n z. gind z IH. intros i H Hz Hr.
  rewrite rng_ok_eq. destruct (bdec (i <? n)) as [Hi | Hi]; [|reflexivity].
  pose proof Hi as Hi'. bnorm. pose proof (succ_lt i n Hi') as Hs.
  destruct (Hr i ltac:(lia)) as [A B].
  replace ((2 <=? x.[i]) && (x.[i] <=? 2000000000)) with true
    by (symmetry; apply andb_true_iff; split; apply leb_true; assumption).
  eapply IH; [ | reflexivity | ]. rewrite <- Hz. apply dec_step. exact Hi.
  intros j Hj. apply Hr. lia.
Qed.

Lemma dec_exists_lt : forall (P : nat -> Prop), (forall v, P v \/ ~ P v) ->
  forall k, (exists v, (v < k)%nat /\ P v) \/ (forall v, (v < k)%nat -> ~ P v).
Proof.
  intros P D k. induction k as [|k IH].
  - right. intros; lia.
  - destruct IH as [[v [Hv Pv]] | N].
    + left. exists v. split; [lia|exact Pv].
    + destruct (D k) as [Pk|Pk].
      * left. exists k. split; [lia|exact Pk].
      * right. intros v Hv. destruct (Nat.eq_dec v k); [subst; exact Pk|]. apply N. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Max-flow min-cut for the final preflow                              *)
(* ------------------------------------------------------------------ *)

Section Flow.
Local Open Scope Z_scope.

Variable N : nat.
Variables s t : nat.
Hypothesis Hs : (s < N)%nat.
Hypothesis Ht : (t < N)%nat.
Hypothesis Hst : s <> t.
Variable c : nat -> nat -> Z.
Hypothesis c_nonneg : forall a b, 0 <= c a b.
Hypothesis c_sym : forall a b, c a b = c b a.
Variable r : nat -> nat -> Z.
Hypothesis r_nonneg : forall a b, (a < N)%nat -> (b < N)%nat -> 0 <= r a b.
Hypothesis r_sym : forall a b, (a < N)%nat -> (b < N)%nat -> r a b + r b a = 2 * c a b.
Variable e : nat -> Z.
Hypothesis e_def : forall v, (v < N)%nat -> v <> s -> e v = zsum (fun a => c a v - r a v) N.
Hypothesis e_nonneg : forall v, (v < N)%nat -> v <> s -> 0 <= e v.
Variable h : nat -> Z.
Hypothesis h_valid : forall a b, (a < N)%nat -> (b < N)%nat -> 0 < r a b -> h a <= h b + 1.
Hypothesis h_s : h s = Z.of_nat N.
Hypothesis h_t : h t = 0.
Hypothesis final : forall v, (v < N)%nat -> v <> s -> v <> t -> 0 < e v -> Z.of_nat N <= h v.
Hypothesis r_t : forall x, (x < N)%nat -> c t x <= r t x.

Definition walk (w : nat -> nat -> Z) : Prop :=
  (forall a b, (a < N)%nat -> (b < N)%nat -> 0 <= w a b <= c a b) /\
  (forall v, (v < N)%nat -> v <> s -> v <> t -> zsum (fun b => w v b) N = zsum (fun b => w b v) N).

Definition wvalue (w : nat -> nat -> Z) : Z := zsum (fun b => w s b) N - zsum (fun b => w b s) N.

(* some height strictly between 0 and N is taken by no vertex *)
Lemma pigeon : exists k, 1 <= k <= Z.of_nat N - 1 /\ forall v, (v < N)%nat -> h v <> k.
Proof.
  destruct (dec_exists_lt (fun k => (forall v, (v < N)%nat -> h v <> Z.of_nat (S k))))
             with (k := (N - 1)%nat) as [[k [Hk P]] | NP].
  - intros k. destruct (dec_exists_lt (fun v => h v = Z.of_nat (S k)) (fun v => Z.eq_decidable (h v) (Z.of_nat (S k))) N)
      as [[v [Hv P]] | P].
    + right. intros A. apply (A v Hv). exact P.
    + left. exact P.
  - exists (Z.of_nat (S k)). split; [lia|exact P].
  - exfalso.
    assert (Hin : forall k, (k < N - 1)%nat -> exists v, (v < N)%nat /\ h v = Z.of_nat (S k)).
    { intros k Hk. specialize (NP k Hk).
      destruct (dec_exists_lt (fun v => h v = Z.of_nat (S k)) (fun v => Z.eq_decidable (h v) (Z.of_nat (S k))) N)
        as [E | E]; [exact E|]. exfalso. apply NP. exact E. }
    set (l := Z.of_nat N :: 0 :: map (fun k => Z.of_nat (S k)) (seq 0 (N - 1))).
    assert (ND : NoDup l).
    { unfold l. constructor; [|constructor].
      - intros [A|A]; [lia|]. apply in_map_iff in A. destruct A as [k [Ek Ik]].
        apply in_seq in Ik. lia.
      - intros A. apply in_map_iff in A. destruct A as [k [Ek Ik]]. lia.
      - apply NoDup_map_NoDup_ForallPairs; [intros a b _ _ E; lia|]. apply seq_NoDup. }
    assert (IN : incl l (map h (seq 0 N))).
    { intros y Hy. apply in_map_iff. unfold l in Hy. destruct Hy as [Hy|[Hy|Hy]].
      - exists s. split; [lia|]. apply in_seq. lia.
      - exists t. split; [lia|]. apply in_seq. lia.
      - apply in_map_iff in Hy. destruct Hy as [k [Ek Ik]]. apply in_seq in Ik.
        destruct (Hin k ltac:(lia)) as [v [Hv Ev]]. exists v. split; [lia|]. apply in_seq. lia. }
    pose proof (NoDup_incl_length ND IN) as LL.
    unfold l in LL. simpl in LL. rewrite length_map, length_seq, length_map, length_seq in LL.
    assert (N >= 2)%nat.
    { destruct (Nat.eq_dec N 0); [lia|]. destruct (Nat.eq_dec N 1); [|lia]. subst. lia. }
    lia.
Qed.

Section Cut.
Variable k : Z.
Hypothesis Hk : 1 <= k <= Z.of_nat N - 1.
Hypothesis Hgap : forall v, (v < N)%nat -> h v <> k.

Definition inS (v : nat) : bool := Z.ltb k (h v).

Lemma cut_sat : forall a b, (a < N)%nat -> (b < N)%nat -> inS a = true -> inS b = false -> r a b = 0.
Proof.
  intros a b Ha Hb A B. unfold inS in *. apply Z.ltb_lt in A. apply Z.ltb_ge in B.
  pose proof (Hgap b Hb). pose proof (r_nonneg a b Ha Hb).
  destruct (Z.eq_dec (r a b) 0) as [E|E]; [exact E|].
  pose proof (h_valid a b Ha Hb ltac:(lia)). lia.
Qed.

Lemma inS_s : inS s = true.
Proof. unfold inS. apply Z.ltb_lt. lia. Qed.

Lemma inS_t : inS t = false.
Proof. unfold inS. apply Z.ltb_ge. lia. Qed.

Definition cutcap : Z :=
  zsum (fun b => if inS b then 0 else zsum (fun a => if inS a then c a b else 0) N) N.

Lemma et_cut : e t = cutcap.
Proof.
  assert (E1 : e t = zsum (fun v => if inS v then 0 else e v) N).
  { rewrite <- (zsum_single t (e t) N Ht). apply zsum_ext. intros v Hv.
    destruct (Nat.eqb_spec v t).
    - subst. rewrite inS_t. reflexivity.
    - destruct (inS v) eqn:Sv; [reflexivity|].
      assert (v <> s) by (intro; subst; rewrite inS_s in Sv; discriminate).
      pose proof (e_nonneg v Hv H). 
      destruct (Z.eq_dec (e v) 0) as [Z0|Z0]; [lia|].
      pose proof (final v Hv H n ltac:(lia)). unfold inS in Sv. apply Z.ltb_ge in Sv. lia. }
  rewrite E1.
  set (g := fun a v => if inS v then 0 else if inS a then 0 else c a v - r a v).
  assert (E2 : zsum (fun v => if inS v then 0 else e v) N
             = zsum (fun v => zsum (fun a => g a v) N) N + cutcap).
  { unfold cutcap. rewrite <- zsum_add. apply zsum_ext. intros v Hv.
    unfold g. destruct (inS v) eqn:Sv.
    - rewrite zsum_zero by (intros; reflexivity). reflexivity.
    - assert (v <> s) by (intro; subst; rewrite inS_s in Sv; discriminate).
      rewrite e_def by assumption. rewrite <- zsum_add. apply zsum_ext. intros a Ha.
      destruct (inS a) eqn:Sa; [|lia]. rewrite cut_sat by assumption. lia. }
  rewrite E2. rewrite zsum_antisym; [lia|].
  intros a b Ha Hb. unfold g. destruct (inS a), (inS b); try lia.
  pose proof (r_sym a b Ha Hb). rewrite (c_sym b a). lia.
Qed.

Lemma walk_cut : forall w, walk w -> wvalue w <= cutcap.
Proof.
  intros w [Wc Wk].
  assert (E1 : wvalue w = zsum (fun a => if inS a then
                 zsum (fun b => w a b) N - zsum (fun b => w b a) N else 0) N).
  { unfold wvalue. rewrite <- (zsum_single s _ N Hs). apply zsum_ext. intros a Ha.
    destruct (Nat.eqb_spec a s).
    - subst. rewrite inS_s. reflexivity.
    - destruct (inS a) eqn:Sa; [|reflexivity].
      assert (a <> t) by (intro; subst; rewrite inS_t in Sa; discriminate).
      rewrite (Wk a Ha n H). lia. }
  set (g := fun b a => if inS a then if inS b then w a b - w b a else 0 else 0).
  assert (E2 : zsum (fun a => if inS a then
                 zsum (fun b => w a b) N - zsum (fun b => w b a) N else 0) N
             = zsum (fun a => zsum (fun b => g b a) N) N +
               zsum (fun a => if inS a then zsum (fun b => if inS b then 0 else w a b - w b a) N else 0) N).
  { rewrite <- zsum_add. apply zsum_ext. intros a Ha. unfold g.
    destruct (inS a).
    - rewrite <- zsum_sub, <- zsum_add. apply zsum_ext. intros b Hb. destruct (inS b); lia.
    - rewrite zsum_zero by (intros; reflexivity). lia. }
  rewrite E1, E2, zsum_antisym.
  2:{ intros a b Ha Hb. unfold g. destruct (inS a), (inS b); lia. }
  assert (E3 : cutcap = zsum (fun a => zsum (fun b =>
                 if inS b then 0 else if inS a then c a b else 0) N) N).
  { unfold cutcap. rewrite zsum_swap. apply zsum_ext. intros b Hb.
    destruct (inS b); [|reflexivity]. rewrite zsum_zero by (intros; reflexivity). reflexivity. }
  rewrite E3. apply zsum_le. intros a Ha.
  destruct (inS a) eqn:Sa.
  - apply zsum_le. intros b Hb. destruct (inS b); [lia|].
    destruct (Wc a b Ha Hb). destruct (Wc b a Hb Ha). lia.
  - apply zsum_nonneg. intros b Hb. destruct (inS b); [lia|]. lia.
Qed.

End Cut.

Theorem flow_upper : forall w, walk w -> wvalue w <= e t.
Proof.
  intros w W. destruct pigeon as [k [Hk Hg]].
  rewrite (et_cut k Hk Hg). apply walk_cut; assumption.
Qed.

(* the stranded excess of the preflow goes back, one unit at a time *)
Definition exs (g : nat -> nat -> Z) (v : nat) : Z := zsum (fun a => g a v) N.

Definition gok (g : nat -> nat -> Z) : Prop :=
  (forall a b, (a < N)%nat -> (b < N)%nat -> g a b = - g b a) /\
  (forall a b, (a < N)%nat -> (b < N)%nat -> g a b <= c a b) /\
  (forall v, (v < N)%nat -> v <> s -> 0 <= exs g v) /\
  (forall x, (x < N)%nat -> g t x <= 0).

Definition pos_mass (g : nat -> nat -> Z) : Z :=
  zsum (fun a => zsum (fun b => Z.max (g a b) 0) N) N.

Definition ind2 (u v a b : nat) : Z := if (Nat.eqb a u && Nat.eqb b v)%bool then 1 else 0.

Lemma zsum_ind2_col : forall u v x, (u < N)%nat ->
  zsum (fun a => ind2 u v a x) N = if Nat.eqb x v then 1 else 0.
Proof.
  intros u v x Hu. unfold ind2. destruct (Nat.eqb_spec x v).
  - subst x. rewrite (zsum_ext _ (fun a => if Nat.eqb a u then 1 else 0)).
    + apply zsum_single. exact Hu.
    + intros a Ha. rewrite andb_true_r. reflexivity.
  - apply zsum_zero. intros a Ha. destruct (Nat.eqb a u); simpl; [|reflexivity].
    replace (Nat.eqb x v) with false by (symmetry; apply Nat.eqb_neq; assumption). reflexivity.
Qed.

Lemma cancel : forall (m : Z) g, pos_mass g = m -> gok g ->
  exists g', gok g' /\ (forall v, (v < N)%nat -> v <> s -> v <> t -> exs g' v = 0) /\
             exs g' t = exs g t.
Proof.
  intros m. induction m as [m IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros g Hm Hg.
  destruct (dec_exists_lt (fun v => v <> s /\ v <> t /\ exs g v <> 0)) with (k := N)
    as [[v [Hv [Vs [Vt Ve]]]] | NE].
  - intros v. destruct (Nat.eq_dec v s), (Nat.eq_dec v t), (Z.eq_dec (exs g v) 0);
      first [right; tauto | left; tauto].
  - destruct Hg as [G1 [G2 [G3 G4]]].
    assert (Pv : 0 < exs g v) by (specialize (G3 v Hv Vs); lia).
    destruct (zsum_pos _ _ Pv) as [u [Hu Pu]].
    assert (Ut : u <> t) by (intro; subst; specialize (G4 v Hv); lia).
    assert (Uv : u <> v) by (intro; subst; specialize (G1 v v Hv Hv); lia).
    set (g' := fun a b => g a b - ind2 u v a b + ind2 v u a b).
    assert (Ex : forall x, (x < N)%nat ->
              exs g' x = exs g x - (if Nat.eqb x v then 1 else 0) + (if Nat.eqb x u then 1 else 0)).
    { intros x Hx. unfold exs, g'. rewrite zsum_add, zsum_sub.
      rewrite (zsum_ind2_col u v x Hu), (zsum_ind2_col v u x Hv). reflexivity. }
    assert (Hg' : gok g').
    { split; [|split; [|split]].
      - intros a b Ha Hb. unfold g', ind2. rewrite (G1 a b Ha Hb).
        destruct (Nat.eqb_spec a u), (Nat.eqb_spec b v), (Nat.eqb_spec a v), (Nat.eqb_spec b u);
          simpl; subst; try lia.
      - intros a b Ha Hb. unfold g', ind2. pose proof (G2 a b Ha Hb). pose proof (c_nonneg a b).
        destruct (Nat.eqb_spec a u), (Nat.eqb_spec b v), (Nat.eqb_spec a v), (Nat.eqb_spec b u);
          simpl; subst; try lia.
        rewrite (G1 v u Hv Hu). lia.
      - intros x Hx Xs. rewrite (Ex x Hx). pose proof (G3 x Hx Xs).
        destruct (Nat.eqb_spec x v), (Nat.eqb_spec x u); subst; lia.
      - intros y Hy. unfold g', ind2. pose proof (G4 y Hy).
        destruct (Nat.eqb_spec t u), (Nat.eqb_spec t v); simpl; try lia; congruence. }
    assert (Pm : pos_mass g' = pos_mass g - 1).
    { unfold pos_mass.
      assert (A : forall a b, (a < N)%nat -> (b < N)%nat ->
                Z.max (g' a b) 0 = Z.max (g a b) 0 - ind2 u v a b).
      { intros a b Ha Hb. unfold g', ind2.
        destruct (Nat.eqb_spec a u), (Nat.eqb_spec b v), (Nat.eqb_spec a v), (Nat.eqb_spec b u);
          simpl; subst; try lia.
        rewrite (G1 v u Hv Hu). lia. }
      rewrite (zsum_ext _ (fun a => zsum (fun b => Z.max (g a b) 0) N - zsum (fun b => ind2 u v a b) N) N).
      2:{ intros a Ha. rewrite <- zsum_sub. apply zsum_ext. intros b Hb. apply A; assumption. }
      rewrite zsum_sub, (zsum_swap (ind2 u v)).
      rewrite (zsum_ext (fun j => zsum (fun i => ind2 u v i j) N) (fun b => if Nat.eqb b v then 1 else 0) N)
        by (intros b Hb; apply zsum_ind2_col; exact Hu).
      rewrite zsum_single by exact Hv. lia. }
    assert (M0 : 0 <= pos_mass g').
    { apply zsum_nonneg. intros a _. apply zsum_nonneg. intros b _. lia. }
    destruct (IH (pos_mass g')) with (g := g') as [g2 [A [B C]]];
      [unfold Zwf; lia | reflexivity | exact Hg' |].
    exists g2. split; [exact A|]. split; [exact B|].
    rewrite C, (Ex t Ht).
    destruct (Nat.eqb_spec t v), (Nat.eqb_spec t u); subst; try congruence. lia.
  - exists g. split; [exact Hg|]. split; [|reflexivity].
    intros v Hv Vs Vt. destruct (Z.eq_dec (exs g v) 0) as [E|E]; [exact E|].
    exfalso. apply (NE v Hv). tauto.
Qed.

Theorem flow_exists : exists w, walk w /\ wvalue w = e t.
Proof.
  set (g0 := fun a b => c a b - r a b).
  assert (G0 : gok g0).
  { split; [|split; [|split]].
    - intros a b Ha Hb. unfold g0. pose proof (r_sym a b Ha Hb). rewrite (c_sym b a). lia.
    - intros a b Ha Hb. unfold g0. pose proof (r_nonneg a b Ha Hb). lia.
    - intros v Hv Vs. unfold exs, g0. rewrite <- e_def by assumption. apply e_nonneg; assumption.
    - intros y Hy. unfold g0. pose proof (r_t y Hy). lia. }
  assert (Et : exs g0 t = e t) by (unfold exs, g0; symmetry; apply e_def; [exact Ht | congruence]).
  destruct (cancel _ g0 eq_refl G0) as [g [[G1 [G2 [G3 G4]]] [Z0 Zt]]].
  exists (fun a b => Z.max (g a b) 0).
  assert (Cons : forall v, (v < N)%nat ->
            zsum (fun b => Z.max (g v b) 0) N - zsum (fun b => Z.max (g b v) 0) N = - exs g v).
  { intros v Hv. unfold exs. rewrite <- zsum_sub, <- zsum_opp. apply zsum_ext. intros b Hb.
    rewrite (G1 b v Hb Hv). lia. }
  split; [split|].
  - intros a b Ha Hb. pose proof (G2 a b Ha Hb). pose proof (c_nonneg a b). lia.
  - intros v Hv Vs Vt. pose proof (Cons v Hv). rewrite (Z0 v Hv Vs Vt) in H. lia.
  - unfold wvalue. rewrite (Cons s Hs).
    assert (T : zsum (fun v => exs g v) N = 0)
      by (unfold exs; apply zsum_antisym; intros; apply G1; assumption).
    rewrite (zsum_ext _ (fun v => (if Nat.eqb v s then exs g s else 0) +
                                  (if Nat.eqb v t then exs g t else 0)) N) in T.
    2:{ intros v Hv. destruct (Nat.eqb_spec v s), (Nat.eqb_spec v t); subst; try congruence; try lia.
        rewrite (Z0 v Hv n n0). lia. }
    rewrite zsum_add, !zsum_single in T by assumption. lia.
Qed.

End Flow.

Lemma Z_gcd_N : forall a b : N, Z.of_N (N.gcd a b) = Z.gcd (Z.of_N a) (Z.of_N b).
Proof. intros [|a] [|b]; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Back to the contract                                                *)
(* ------------------------------------------------------------------ *)

Lemma io_back : forall u, io (Z.to_nat (φ u)) = u.
Proof.
  intros u. bnd u. apply int_eq. rewrite io_spec by (rewrite Z2Nat.id; lia).
  apply Z2Nat.id. lia.
Qed.

Lemma io_val : forall k, (Z.of_nat k < 4194304)%Z -> (φ (io k)) = Z.of_nat k.
Proof. intros k Hk. apply io_spec. rewrite wB_val. lia. Qed.

Lemma sb_zsum : forall f m, Z.of_N (sum_below f m) = zsum (fun k => Z.of_N (f (N.of_nat k))) m.
Proof. intros f m. induction m as [|m IH]; simpl; [reflexivity|]. rewrite N2Z.inj_add, IH. reflexivity. Qed.

Lemma minmax : forall x, (1 <= (φ (nn x)))%Z ->
  ((φ (ss x)) < (φ (nn x)))%Z /\ ((φ (tt x)) < (φ (nn x)))%Z /\
  (forall j, ((φ j) < (φ (nn x)))%Z -> ((φ (x.[ss x])) <= (φ (x.[j])))%Z) /\
  (forall j, ((φ j) < (φ (nn x)))%Z -> ((φ (x.[j])) <= (φ (x.[tt x])))%Z).
Proof.
  intros x H1.
  assert (St : forall j, ((φ j) < (φ 1))%Z -> ((φ j) < (φ (nn x)))%Z -> j = 0).
  { intros j A _. change (φ 1) with 1%Z in A. bnd j. apply int_eq. change (φ 0) with 0%Z. lia. }
  destruct (amin_spec x (nn x) _ 1 0 (wf0 (nn x) 1) eq_refl ltac:(change (φ 0) with 0%Z; lia)
              ltac:(intros j A B; rewrite (St j A B); lia)) as [A1 A2].
  destruct (amax_spec x (nn x) _ 1 0 (wf0 (nn x) 1) eq_refl ltac:(change (φ 0) with 0%Z; lia)
              ltac:(intros j A B; rewrite (St j A B); lia)) as [B1 B2].
  unfold ss, tt. tauto.
Qed.

Section Final.

Variable rooms : list N.
Variable x : array int.
Hypothesis Hv : valid_input rooms.
Hypothesis Hr : repr (x : array uint) rooms.

Local Notation L := (List.length rooms).

Lemma f_len : (φ (nn x)) = Z.of_nat L.
Proof. destruct Hr as [Hl _]. symmetry. exact Hl. Qed.

Lemma f_cell : forall k, (k < L)%nat -> Z.of_N (nth k rooms 0%N) = (φ (x.[io k])).
Proof.
  intros k Hk. destruct Hr as [_ Hc]. destruct (Hc k Hk) as [m [Hm Rm]].
  unfold repr, repr_uint in Rm. rewrite (nth_error_nth _ _ _ Hm). rewrite <- Rm.
  rewrite Z2N.id by (apply to_Z_bounded). reflexivity.
Qed.

Lemma f_bounds : (2 <= Z.of_nat L <= 1000)%Z.
Proof. destruct Hv as [Hn _ _ _]. unfold len in Hn. lia. Qed.

Lemma f_range : forall j, ((φ j) < (φ (nn x)))%Z -> (2 <= (φ (x.[j])) <= 2000000000)%Z.
Proof.
  intros j Hj. rewrite f_len in Hj. bnd j.
  rewrite <- (io_back j). rewrite <- f_cell by lia.
  destruct Hv as [_ Hrg _ _]. rewrite Forall_nth in Hrg.
  specialize (Hrg (Z.to_nat (φ j)) 0%N ltac:(lia)). lia.
Qed.

Lemma f_inj : forall a b, (a < L)%nat -> (b < L)%nat -> (φ (x.[io a])) = (φ (x.[io b])) -> a = b.
Proof.
  intros a b Ha Hb E. rewrite <- !f_cell in E by assumption.
  destruct Hv as [_ _ Hu _]. apply (proj1 (NoDup_nth rooms 0%N) Hu a b Ha Hb). lia.
Qed.

Lemma f_guard : guard x = true.
Proof.
  pose proof f_len as Lx. pose proof f_bounds as B.
  destruct (minmax x ltac:(lia)) as [A1 [B1 [A2 B2]]].
  unfold guard. apply andb_true_iff. split; [apply andb_true_iff; split; [apply andb_true_iff; split|]|].
  - apply leb_true. change (φ 2) with 2%Z. lia.
  - apply leb_true. change (φ 1000) with 1000%Z. lia.
  - apply (rng_ok_complete x (nn x) _ 0 (wf0 (nn x) 0) eq_refl). intros j Hj. apply f_range. lia.
  - apply negb_true_iff. apply eqb_false. intros E.
    assert (E0 : (φ (x.[io 0])) = (φ (x.[io 1]))).
    { assert (L0 : ((φ (io 0)) < (φ (nn x)))%Z) by (rewrite io_val by lia; lia).
      assert (L1 : ((φ (io 1)) < (φ (nn x)))%Z) by (rewrite io_val by lia; lia).
      pose proof (A2 _ L0). pose proof (A2 _ L1). pose proof (B2 _ L0). pose proof (B2 _ L1).
      rewrite E in *. lia. }
    apply f_inj in E0; lia.
Qed.

Lemma f_cap : forall a b, (a < L)%nat -> (b < L)%nat ->
  Z.of_N (cap rooms (N.of_nat a) (N.of_nat b)) = cpx x (nn x) (io a) (io b).
Proof.
  intros a b Ha Hb. pose proof f_len as Lx. pose proof f_bounds as B.
  assert (Ia : (φ (io a)) = Z.of_nat a) by (apply io_val; lia).
  assert (Ib : (φ (io b)) = Z.of_nat b) by (apply io_val; lia).
  rewrite cp_lt by lia. unfold cap, capf, room. rewrite !Nnat.Nat2N.id.
  destruct (Nat.eq_dec a b) as [E|E].
  - subst b. rewrite N.eqb_refl, eqb_refl. reflexivity.
  - replace (N.of_nat a =? N.of_nat b)%N with false by (symmetry; apply N.eqb_neq; lia).
    replace (io a =? io b) with false by (symmetry; apply eqb_false; intro X; apply E;
      apply (f_equal to_Z) in X; lia).
    pose proof (igcd_spec x.[io a] x.[io b]) as G.
    rewrite <- (f_cell a Ha), <- (f_cell b Hb), <- Z_gcd_N in G.
    destruct (1 <? igcd x.[io a] x.[io b]) eqn:E1; bnorm; change (φ 1) with 1%Z in *.
    + replace (1 <? N.gcd (nth a rooms 0%N) (nth b rooms 0%N))%N with true by (symmetry; apply N.ltb_lt; lia).
      lia.
    + replace (1 <? N.gcd (nth a rooms 0%N) (nth b rooms 0%N))%N with false by (symmetry; apply N.ltb_ge; lia).
      reflexivity.
Qed.

Theorem mazemovement_impl_correct :
  exists ans : N, repr (mazemovement_impl x) ans /\ mazemovement_spec rooms ans.
Proof.
  pose proof f_guard as Hg.
  destruct (guard_facts x Hg) as [Hn [Hs [Ht [Hst [Hx' [Hmin Hmax]]]]]].
  pose proof f_len as Lx.
  unfold mazemovement_impl. destruct (bdec (guard x)) as [Hg' | Hg']; [|congruence].
  destruct (mloop_spec (nn x) (ss x) (tt x) (cpx x (nn x)) Hn Hs Ht Hst (cp_rng (nn x) 0 0 x Hx')
              _ (acc_init x Hg') _ _ _ _ _ _ _ _ _ _ (acc_init x Hg') eq_refl (init_inv x Hg'))
    as [S' [I' [NA R]]].
  cbv zeta. rewrite R.
  exists (Z.to_N (φ ((s_ex S').[tt x]))). split; [reflexivity|].
  destruct I' as [T [Hh [_ _]]].
  set (n := nn x) in *. set (sn := Z.to_nat (φ (ss x))). set (tn := Z.to_nat (φ (tt x))).
  assert (Ns : io sn = ss x) by apply io_back.
  assert (Nt : io tn = tt x) by apply io_back.
  assert (Hsn : (sn < L)%nat) by lia. assert (Htn : (tn < L)%nat) by lia.
  assert (Hstn : sn <> tn) by (intro E; apply Hst; rewrite <- Ns, <- Nt, E; reflexivity).
  assert (IL : forall k, (k < L)%nat -> ((φ (io k)) < (φ n))%Z /\ (φ (io k)) = Z.of_nat k)
    by (intros k Hk; rewrite io_val by lia; lia).
  intros s' t' Hen Hex.
  (* the entrance and the exit are the code's s and t *)
  assert (Es : s' = N.of_nat sn).
  { destruct Hen as [H1 H2]. unfold len in H1.
    pose proof (H2 (N.of_nat sn) ltac:(unfold len; lia)) as A. unfold room in A.
    rewrite Nnat.Nat2N.id in A. apply N2Z.inj_le in A.
    rewrite !f_cell in A by lia. rewrite Ns in A.
    pose proof (Hmin (io (N.to_nat s')) ltac:(apply IL; lia)).
    assert (N.to_nat s' = sn) by (apply f_inj; [lia | lia | rewrite Ns; lia]). lia. }
  assert (Et : t' = N.of_nat tn).
  { destruct Hex as [H1 H2]. unfold len in H1.
    pose proof (H2 (N.of_nat tn) ltac:(unfold len; lia)) as A. unfold room in A.
    rewrite Nnat.Nat2N.id in A. apply N2Z.inj_le in A.
    rewrite !f_cell in A by lia. rewrite Nt in A.
    pose proof (Hmax (io (N.to_nat t')) ltac:(apply IL; lia)).
    assert (N.to_nat t' = tn) by (apply f_inj; [lia | lia | rewrite Nt; lia]). lia. }
  subst s' t'. clear Hen Hex.
  (* the abstract flow facts *)
  set (cF := fun a b => cpx x n (io a) (io b)).
  set (rF := fun a b => RD n (s_tbl S') (io a) (io b)).
  set (eF := fun v => (φ ((s_ex S').[io v]))).
  set (hF := fun v => (φ ((s_h S').[io v]))).
  assert (NL : Z.to_nat (φ n) = L) by lia.
  assert (c_nonneg : forall a b, (0 <= cF a b)%Z) by (intros; apply (cp_rng n 0 0 x Hx')).
  assert (c_sym : forall a b, cF a b = cF b a) by (intros; apply cp_sym).
  assert (r_nonneg : forall a b, (a < L)%nat -> (b < L)%nat -> (0 <= rF a b)%Z)
    by (intros; unfold rF, RD; apply to_Z_bounded).
  assert (r_sym : forall a b, (a < L)%nat -> (b < L)%nat -> (rF a b + rF b a = 2 * cF a b)%Z)
    by (intros a b Ha Hb; apply (t_sym _ _ _ _ _ _ T); apply IL; assumption).
  assert (e_def : forall v, (v < L)%nat -> v <> sn -> eF v = zsum (fun a => (cF a v - rF a v)%Z) L).
  { intros v Hv1 Vs. unfold eF. rewrite (t_ex _ _ _ _ _ _ T); [| apply IL; exact Hv1 |].
    - unfold colsum, isum. rewrite NL. reflexivity.
    - intros E. apply Vs. rewrite <- Ns in E. apply (f_equal to_Z) in E.
      destruct (IL v Hv1) as [_ A]. destruct (IL sn Hsn) as [_ B]. lia. }
  assert (e_nonneg : forall v, (v < L)%nat -> v <> sn -> (0 <= eF v)%Z)
    by (intros; unfold eF; apply to_Z_bounded).
  assert (r_t : forall y, (y < L)%nat -> (cF tn y <= rF tn y)%Z).
  { intros y Hy. unfold cF, rF. rewrite Nt. apply (t_t _ _ _ _ _ _ T). apply IL. exact Hy. }
  assert (h_valid : forall a b, (a < L)%nat -> (b < L)%nat -> (0 < rF a b)%Z -> (hF a <= hF b + 1)%Z)
    by (intros a b Ha Hb Rab; apply (h_valid _ _ _ _ _ Hh); try apply IL; assumption).
  assert (h_s : hF sn = Z.of_nat L) by (unfold hF; rewrite Ns, (h_s _ _ _ _ _ Hh); lia).
  assert (h_t : hF tn = 0%Z) by (unfold hF; rewrite Nt, (h_t _ _ _ _ _ Hh); reflexivity).
  assert (final : forall v, (v < L)%nat -> v <> sn -> v <> tn -> (0 < eF v)%Z -> (Z.of_nat L <= hF v)%Z).
  { intros v Hv1 Vs Vt Pe. destruct (Z_lt_le_dec (hF v) (Z.of_nat L)) as [Lh|Lh]; [|exact Lh].
    exfalso. destruct (IL v Hv1) as [Lv Iv].
    pose proof (NA (io v) Lv) as A. unfold active in A. unfold eF, hF in *.
    assert (Ds : io v <> ss x) by (intro E; apply Vs; rewrite <- Ns in E; apply (f_equal to_Z) in E;
                                   destruct (IL sn Hsn); lia).
    assert (Dt : io v <> tt x) by (intro E; apply Vt; rewrite <- Nt in E; apply (f_equal to_Z) in E;
                                   destruct (IL tn Htn); lia).
    replace (0 <? (s_ex S').[io v]) with true in A by (symmetry; apply ltb_true; exact Pe).
    replace ((s_h S').[io v] <? n) with true in A by (symmetry; apply ltb_true; lia).
    replace (io v =? ss x) with false in A by (symmetry; apply eqb_false; exact Ds).
    replace (io v =? tt x) with false in A by (symmetry; apply eqb_false; exact Dt).
    discriminate A. }
  assert (Cap : forall a b, (a < L)%nat -> (b < L)%nat -> Z.of_N (cap rooms (N.of_nat a) (N.of_nat b)) = cF a b)
    by (intros; apply f_cap; assumption).
  assert (Ans : Z.of_N (Z.to_N (φ ((s_ex S').[tt x]))) = eF tn)
    by (unfold eF; rewrite Nt; apply Z2N.id; apply to_Z_bounded).
  split.
  - destruct (flow_exists L sn tn Hsn Htn Hstn cF c_nonneg c_sym rF r_nonneg r_sym eF e_def e_nonneg r_t)
      as [w [[Wc Wk] Wv]].
    exists (fun i j => Z.to_N (w (N.to_nat i) (N.to_nat j))). split; [split|].
    + intros i j Hi Hj. unfold len in Hi, Hj.
      destruct (Wc (N.to_nat i) (N.to_nat j) ltac:(lia) ltac:(lia)) as [W1 W2].
      rewrite <- (Cap (N.to_nat i) (N.to_nat j)) in W2 by lia. rewrite !Nnat.N2Nat.id in W2. lia.
    + intros v Hv1 Vs Vt. unfold len in Hv1. apply N2Z.inj. unfold outflow, inflow. rewrite !sb_zsum.
      rewrite (zsum_ext _ (fun k => w (N.to_nat v) k)), (zsum_ext (fun k => Z.of_N (Z.to_N (w (N.to_nat (N.of_nat k)) (N.to_nat v)))) (fun k => w k (N.to_nat v))).
      * apply Wk; lia.
      * intros k Hk. rewrite Nnat.Nat2N.id. apply Z2N.id. apply Wc; lia.
      * intros k Hk. rewrite Nnat.Nat2N.id. apply Z2N.id. apply Wc; lia.
    + unfold entering, outflow, inflow. rewrite !sb_zsum, Ans, <- Wv. unfold wvalue.
      rewrite !Nnat.Nat2N.id.
      rewrite (zsum_ext _ (fun k => w sn k)), (zsum_ext (fun k => Z.of_N (Z.to_N (w (N.to_nat (N.of_nat k)) sn))) (fun k => w k sn)).
      * reflexivity.
      * intros k Hk. rewrite Nnat.Nat2N.id. apply Z2N.id. apply Wc; lia.
      * intros k Hk. rewrite Nnat.Nat2N.id. apply Z2N.id. apply Wc; lia.
  - intros W [Wc Wk]. rewrite Ans.
    set (w := fun a b => Z.of_N (W (N.of_nat a) (N.of_nat b))).
    assert (WW : walk L sn tn cF w).
    { split.
      - intros a b Ha Hb. unfold w. rewrite <- Cap by assumption.
        pose proof (Wc (N.of_nat a) (N.of_nat b) ltac:(unfold len; lia) ltac:(unfold len; lia)). lia.
      - intros v Hv1 Vs Vt.
        pose proof (Wk (N.of_nat v) ltac:(unfold len; lia) ltac:(lia) ltac:(lia)) as K.
        unfold outflow, inflow in K. apply (f_equal Z.of_N) in K. rewrite !sb_zsum in K. exact K. }
    pose proof (flow_upper L sn tn Hsn Htn Hstn cF c_sym rF r_nonneg r_sym eF e_def e_nonneg hF
                  h_valid h_s h_t final r_t w WW) as U.
    unfold wvalue in U. unfold entering, outflow, inflow. rewrite !sb_zsum. exact U.
Qed.

End Final.

Definition mazemovement_correct : forall (rooms : list N) (x : array uint),
  valid_input rooms -> repr x rooms ->
  exists ans : N, repr (mazemovement x) ans /\ mazemovement_spec rooms ans
  := fun rooms x Hv Hr => mazemovement_impl_correct rooms x Hv Hr.
