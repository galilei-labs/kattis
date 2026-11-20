(* Implementation of canonical (canonical.spec): is a coin system
   canonical (the greedy algorithm always optimal)?

   Code.  With B = c_n + c_(n-1) (the Kozen-Zaks bound), one bottom-up pass
   over the amounts x = 1 .. B-1 fills two flat tables of length B:
   - t.[x], the minimum number of coins for x (unbounded-knapsack DP):
     1 + min over the coins c_j <= x of t.[x - c_j];
   - g.[x], the greedy count for x: 1 + g.[x - c_k] where c_k is the
     largest coin <= x.  The index k is a pointer that only moves forward
     (at most one step per amount, the coins being strictly increasing),
     so the greedy count costs O(1) per amount.
   The pass stops with false at the first amount where t.[x] < g.[x], and
   answers true when none is found below B.

   Proof.  The tables meet the math side (min_coins, greedy_uses) on every
   amount below x (outer_spec).  The reduction to the bound B is the
   Kozen-Zaks argument (kz): if greedy is optimal below c_n + c_(n-1), it
   is optimal everywhere, by strong induction on the amount.

   Termination: both loops recurse on an erased [Acc (Zwf 0) (gap m i)]
   proof, the template's device.  No nat, no Z in the code. *)

From Canonical.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From KattisLib Require Import Cost.
Import ListNotations.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ------------------------------------------------------------------ *)
(* Math side: coins, sums, greedy, and the Kozen-Zaks bound            *)
(* ------------------------------------------------------------------ *)

Section Math.
Open Scope N_scope.

Variable cs : list N.
Hypothesis Hv : valid_input cs.

Lemma coin_in : forall k, k < len cs -> In (coin cs k) cs.
Proof. intros k Hk. unfold coin, len in *. apply nth_In. lia. Qed.

Lemma in_coin : forall d, In d cs -> exists k, k < len cs /\ coin cs k = d.
Proof.
  intros d H. apply (In_nth cs d 0) in H. destruct H as [k [Hk Hn]].
  exists (N.of_nat k). unfold coin, len. rewrite Nat2N.id. split; [lia | exact Hn].
Qed.

Lemma coin_lt : forall j k, j < k -> k < len cs -> coin cs j < coin cs k.
Proof.
  assert (H : forall (d : nat) j, j + N.of_nat d + 1 < len cs ->
                coin cs j < coin cs (j + N.of_nat d + 1)).
  { induction d as [| d IH]; intros j Hj.
    - replace (j + N.of_nat 0 + 1) with (j + 1) by lia.
      apply (vi_increasing _ Hv). lia.
    - specialize (IH j ltac:(lia)).
      pose proof (vi_increasing _ Hv (j + N.of_nat d + 1) ltac:(lia)) as E.
      replace (j + N.of_nat (S d) + 1) with (j + N.of_nat d + 1 + 1) by lia.
      lia. }
  intros j k Hjk Hk. specialize (H (N.to_nat (k - j - 1)) j).
  replace (j + N.of_nat (N.to_nat (k - j - 1)) + 1) with k in H by lia.
  apply H. exact Hk.
Qed.

Lemma coin_le : forall j k, j <= k -> k < len cs -> coin cs j <= coin cs k.
Proof.
  intros j k Hjk Hk. destruct (N.eq_dec j k) as [-> | E]; [lia|].
  pose proof (coin_lt j k ltac:(lia) Hk). lia.
Qed.

Lemma len_ge2 : 2 <= len cs.
Proof. destruct Hv as [[H _] _ _ _]. exact H. Qed.

Lemma coin_pos : forall d, In d cs -> 1 <= d.
Proof.
  intros d Hd. destruct (in_coin d Hd) as [k [Hk <-]].
  pose proof (coin_le 0 k ltac:(lia) Hk). rewrite (vi_first _ Hv) in H. exact H.
Qed.

Lemma coin_max : forall k, k < len cs -> coin cs k <= 10 ^ 6.
Proof.
  intros k Hk. pose proof (vi_max _ Hv) as F. rewrite Forall_forall in F.
  apply F. apply coin_in. exact Hk.
Qed.

Lemma sums_le : forall x m, sums_to cs x m -> m <= x.
Proof.
  induction 1 as [| d x m Hd _ IH]; [lia|].
  pose proof (coin_pos d Hd). lia.
Qed.

Lemma sums_inv : forall x m, sums_to cs x m -> 0 < x ->
  exists d m', In d cs /\ d <= x /\ sums_to cs (x - d) m' /\ m = m' + 1.
Proof.
  intros x m H. destruct H as [| d x m Hd Hs]; intros Hx; [lia|].
  exists d, m. replace (x + d - d) with x by lia. repeat split; auto; lia.
Qed.

Lemma largest_unique : forall x d1 d2,
  largest_le cs x d1 -> largest_le cs x d2 -> d1 = d2.
Proof.
  intros x d1 d2 [H1 [H2 H3]] [H4 [H5 H6]].
  specialize (H3 d2 H4 H5). specialize (H6 d1 H1 H2). lia.
Qed.

Lemma greedy_zero : forall g, greedy_uses cs 0 g -> g = 0.
Proof. intros g H. inversion H; [reflexivity | lia]. Qed.

Lemma greedy_fun : forall x g1, greedy_uses cs x g1 ->
  forall g2, greedy_uses cs x g2 -> g1 = g2.
Proof.
  induction 1 as [| x d g Hx Hd Hg IH]; intros g2 H2.
  - symmetry. apply greedy_zero. exact H2.
  - inversion H2 as [E1 E2 | x' d' g' Hx' Hd' Hg' E1 E2]; [lia|].
    subst. rewrite (largest_unique x d' d Hd' Hd) in Hg'.
    rewrite (IH g' Hg'). reflexivity.
Qed.

Lemma greedy_sums : forall x g, greedy_uses cs x g -> sums_to cs x g.
Proof.
  induction 1 as [| x d g Hx [Hd [Hdx _]] Hg IH]; [constructor|].
  replace (sums_to cs x (g + 1)) with (sums_to cs (x - d + d) (g + 1))
    by (f_equal; lia).
  constructor; assumption.
Qed.

Lemma largest_exists : forall (l : list N) x,
  (forall e, In e l -> x < e) \/
  exists d, In d l /\ d <= x /\ forall e, In e l -> e <= x -> e <= d.
Proof.
  intros l x. induction l as [| a l IH].
  - left. intros e [].
  - destruct IH as [IH | (d & Hd & Hdx & Hmax)].
    + destruct (N.le_gt_cases a x) as [Ha | Ha].
      * right. exists a. split; [left; reflexivity|]. split; [exact Ha|].
        intros e [<- | He] Hex; [lia|]. specialize (IH e He). lia.
      * left. intros e [<- | He]; [exact Ha | apply IH; exact He].
    + right. destruct (N.le_gt_cases a x) as [Ha | Ha].
      * destruct (N.le_gt_cases a d) as [Had | Had].
        -- exists d. split; [right; exact Hd|]. split; [exact Hdx|].
           intros e [<- | He] Hex; [exact Had | apply Hmax; assumption].
        -- exists a. split; [left; reflexivity|]. split; [exact Ha|].
           intros e [<- | He] Hex; [lia|]. specialize (Hmax e He Hex). lia.
      * exists d. split; [right; exact Hd|]. split; [exact Hdx|].
        intros e [<- | He] Hex; [lia | apply Hmax; assumption].
Qed.

Lemma one_in : In 1 cs.
Proof.
  rewrite <- (vi_first _ Hv). apply coin_in. pose proof len_ge2. lia.
Qed.

Lemma greedy_exists : forall x, exists g, greedy_uses cs x g.
Proof.
  intros x. induction x as [x IH] using (well_founded_induction N.lt_wf_0).
  destruct (N.eq_dec x 0) as [-> | Hx]; [exists 0; constructor|].
  destruct (largest_exists cs x) as [H | (d & Hd & Hdx & Hmax)].
  - specialize (H 1 one_in). lia.
  - pose proof (coin_pos d Hd).
    destruct (IH (x - d) ltac:(lia)) as [g Hg].
    exists (g + 1). apply (greedy_step cs x d g); [lia | | exact Hg].
    split; [exact Hd|]. split; assumption.
Qed.

Definition cmax : N := coin cs (len cs - 1).
Definition cmax1 : N := coin cs (len cs - 2).

Lemma le_cmax : forall e, In e cs -> e <= cmax.
Proof.
  intros e He. destruct (in_coin e He) as [k [Hk <-]].
  apply coin_le; lia.
Qed.

Lemma le_cmax1 : forall e, In e cs -> e <> cmax -> e <= cmax1.
Proof.
  intros e He Hne. destruct (in_coin e He) as [k [Hk <-]].
  destruct (N.eq_dec k (len cs - 1)) as [-> | Ek]; [contradiction|].
  apply coin_le; pose proof len_ge2; lia.
Qed.

Lemma cmax_pos : 1 <= cmax /\ 1 <= cmax1.
Proof.
  pose proof len_ge2.
  split; apply coin_pos, coin_in; lia.
Qed.

Lemma greedy_big : forall x g, cmax <= x -> greedy_uses cs x g ->
  exists g', greedy_uses cs (x - cmax) g' /\ g = g' + 1.
Proof.
  intros x g Hx Hg. pose proof cmax_pos as [Hc _].
  inversion Hg as [E1 E2 | x' d g' Hx' Hd Hg' E1 E2]; [lia|]. subst.
  assert (Hl : largest_le cs x cmax).
  { split; [apply coin_in; pose proof len_ge2; lia|]. split; [exact Hx|].
    intros e He _. apply le_cmax. exact He. }
  rewrite (largest_unique x d cmax Hd Hl) in Hg'.
  exists g'. split; [exact Hg' | reflexivity].
Qed.

(* Greedy is optimal at x. *)
Definition gopt (x : N) : Prop :=
  forall m g, sums_to cs x m -> greedy_uses cs x g -> g <= m.

(* Kozen-Zaks: optimal below c_n + c_(n-1) implies optimal everywhere. *)
Theorem kz : (forall x, x < cmax + cmax1 -> gopt x) -> forall x, gopt x.
Proof.
  intros Hsmall x.
  induction x as [x IH] using (well_founded_induction N.lt_wf_0).
  destruct (N.lt_ge_cases x (cmax + cmax1)) as [Hlt | Hge];
    [apply Hsmall; exact Hlt|].
  pose proof cmax_pos as [Hc Hc1].
  intros m g Hs Hg.
  destruct (sums_inv x m Hs ltac:(lia)) as (d & m' & Hd & Hdx & Hs' & ->).
  destruct (greedy_big x g ltac:(lia) Hg) as (gw & Hgw & ->).
  destruct (N.eq_dec d cmax) as [-> | Hne].
  - specialize (IH (x - cmax) ltac:(lia) m' gw Hs' Hgw). lia.
  - pose proof (le_cmax1 d Hd Hne) as Hd1. pose proof (coin_pos d Hd).
    destruct (greedy_exists (x - d)) as [gy Hgy].
    pose proof (IH (x - d) ltac:(lia) m' gy Hs' Hgy) as Hgym.
    destruct (greedy_big (x - d) gy ltac:(lia) Hgy) as (gz & Hgz & ->).
    pose proof (greedy_sums _ _ Hgz) as Hsz.
    assert (Hsw : sums_to cs (x - cmax) (gz + 1)).
    { replace (x - cmax) with (x - d - cmax + d) by lia.
      apply sums_cons; assumption. }
    pose proof (IH (x - cmax) ltac:(lia) _ _ Hsw Hgw). lia.
Qed.

Corollary no_counterexample :
  (forall x, x < cmax + cmax1 -> gopt x) -> forall x, ~ counterexample cs x.
Proof.
  intros H x (_ & m & g & [Hm _] & Hg & Hlt).
  pose proof (kz H x m g Hm Hg). lia.
Qed.

(* One DP step: 1 + the minimum over the coins at most x. *)
Lemma min_step : forall (T : N -> N) x a d0,
  0 < x -> In d0 cs -> d0 <= x ->
  (forall y, y < x -> min_coins cs y (T y)) ->
  T (x - d0) = a ->
  (forall d, In d cs -> d <= x -> a <= T (x - d)) ->
  min_coins cs x (a + 1).
Proof.
  intros T x a d0 Hx Hd0 Hd0x Hmin Ha Hall.
  pose proof (coin_pos d0 Hd0).
  split.
  - destruct (Hmin (x - d0) ltac:(lia)) as [Hs _]. rewrite Ha in Hs.
    replace x with (x - d0 + d0) at 1 by lia. constructor; assumption.
  - intros m' Hs. destruct (sums_inv x m' Hs Hx) as (d & m'' & Hd & Hdx & Hs' & ->).
    pose proof (coin_pos d Hd).
    destruct (Hmin (x - d) ltac:(lia)) as [_ Hm].
    specialize (Hm m'' Hs'). specialize (Hall d Hd Hdx). lia.
Qed.

End Math.

(* ------------------------------------------------------------------ *)
(* Uint63 / PArray plumbing                                            *)
(* ------------------------------------------------------------------ *)

Open Scope uint63_scope.
Open Scope array_scope.

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma alength_set : forall (t : array int) (i : int) (b : int),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set int t i b). Qed.

Lemma aget_set_same : forall (t : array int) (i : int) (b : int),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same int t i b H). Qed.

Lemma aget_set_other : forall (t : array int) (i j : int) (b : int),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other int t i j b H). Qed.

Lemma aget_make : forall (n : int) (b : int) (i : int), (PArray.make n b).[i] = b.
Proof. intros n b i. exact (get_make int b n i). Qed.

Lemma alength_make : forall (n : int) (b : int),
  PArray.length (PArray.make n b)
  = if n <=? PArray.max_length then n else PArray.max_length.
Proof. intros n b. exact (length_make int n b). Qed.

Lemma max_length_val : (φ PArray.max_length) = 4194303%Z.
Proof. reflexivity. Qed.

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

Definition gap (m j : int) : Z := ((φ m) - (φ j))%Z.

Lemma dec_step : forall m i : int,
  (i <? m) = true -> Zwf 0 (gap m (i + 1)) (gap m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* min(acc, min_{j <= i < hi} t.[x - c.[i]]) *)
Fixpoint minloop (c t : array int) (x hi j acc : int)
    (H : Acc (Zwf 0) (gap hi j)) {struct H} : int :=
  match bdec (j <? hi) with
  | left Hj =>
      let v := t.[x - c.[j]] in
      minloop c t x hi (j + 1) (if v <? acc then v else acc)
        (Acc_inv H (dec_step hi j Hj))
  | right _ => acc
  end.
Elpi complexity minloop.
Arguments minloop_cost : simpl never.

Lemma minloop_eq : forall c t x hi j acc H,
  minloop c t x hi j acc H =
  match bdec (j <? hi) with
  | left Hj =>
      let v := t.[x - c.[j]] in
      minloop c t x hi (j + 1) (if v <? acc then v else acc)
        (Acc_inv H (dec_step hi j Hj))
  | right _ => acc
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* The largest-coin pointer for amount x, from the one of amount x - 1. *)
Definition kupd (c : array int) (n x k : int) : int :=
  if k + 1 <? n then (if c.[k + 1] <=? x then k + 1 else k) else k.
Elpi complexity kupd.
Arguments kupd_cost : simpl never.

(* Amounts x, x+1, ..., B-1. *)
Fixpoint outer (c : array int) (n B x k : int) (t g : array int)
    (H : Acc (Zwf 0) (gap B x)) {struct H} : bool :=
  match bdec (x <? B) with
  | left Hx =>
      let k' := kupd c n x k in
      let gx := g.[x - c.[k']] + 1 in
      let tx := minloop c t x (k' + 1) 1 t.[x - 1]
                  (Zwf_well_founded 0 (gap (k' + 1) 1)) + 1 in
      if tx <? gx then false
      else outer c n B (x + 1) k' t.[x <- tx] g.[x <- gx]
             (Acc_inv H (dec_step B x Hx))
  | right _ => true
  end.
Elpi complexity outer.
Arguments outer_cost : simpl never.

Lemma outer_eq : forall c n B x k t g H,
  outer c n B x k t g H =
  match bdec (x <? B) with
  | left Hx =>
      let k' := kupd c n x k in
      let gx := g.[x - c.[k']] + 1 in
      let tx := minloop c t x (k' + 1) 1 t.[x - 1]
                  (Zwf_well_founded 0 (gap (k' + 1) 1)) + 1 in
      if tx <? gx then false
      else outer c n B (x + 1) k' t.[x <- tx] g.[x <- gx]
             (Acc_inv H (dec_step B x Hx))
  | right _ => true
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* The Kozen-Zaks bound c_n + c_(n-1). *)
Definition bound (c : array int) : int :=
  let n := PArray.length c in c.[n - 1] + c.[n - 2].
Elpi complexity bound.
Arguments bound_cost : simpl never.

Definition run (c : array int) : bool :=
  let B := bound c in
  outer c (PArray.length c) B 1 0 (PArray.make B 0) (PArray.make B 0)
    (Zwf_well_founded 0 (gap B 1)).
Elpi complexity run.
Arguments run_cost : simpl never.

Definition canonical_impl (c : array uint) : bool := run c.
Elpi complexity canonical_impl.
Arguments canonical_impl_cost : simpl never.

(* ------------------------------------------------------------------ *)
(* Prop side                                                           *)
(* ------------------------------------------------------------------ *)

(* The N read of a machine word, and the word of an N index. *)
Definition val (v : int) : N := Z.to_N (φ v).
Definition ix (y : N) : int := of_Z (Z.of_N y).
Definition tv (t : array int) (y : N) : N := val t.[ix y].

Lemma ix_eq : forall (i : int) (y : N), (φ i) = Z.of_N y -> i = ix y.
Proof.
  intros i y H. apply to_Z_inj. unfold ix. rewrite of_Z_spec, <- H.
  pose proof (to_Z_bounded i). rewrite Z.mod_small; lia.
Qed.

Lemma val_ix : forall y : N, (Z.of_N y < wB)%Z -> val (ix y) = y.
Proof.
  intros y H. unfold val, ix. rewrite of_Z_spec, Z.mod_small by lia. lia.
Qed.

Lemma tv_set : forall (t : array int) (x v : int) (y : N),
  ((φ x) < (φ (PArray.length t)))%Z -> (Z.of_N y < wB)%Z ->
  tv t.[x <- v] y = if N.eqb y (val x) then val v else tv t y.
Proof.
  intros t x v y Hx Hy. unfold tv.
  destruct (N.eqb_spec y (val x)) as [E | E].
  - assert (ix y = x).
    { symmetry. apply ix_eq. unfold val in E. pose proof (to_Z_bounded x). lia. }
    rewrite H. rewrite aget_set_same; [reflexivity|]. rewrite ltb_spec. exact Hx.
  - rewrite aget_set_other; [reflexivity|].
    intro F. apply E. rewrite F. symmetry. apply val_ix. exact Hy.
Qed.

Lemma tv_make : forall (B v : int) (y : N), tv (PArray.make B v) y = val v.
Proof. intros. unfold tv. rewrite aget_make. reflexivity. Qed.

Section Machine.

Variable cs : list N.
Variable c : array int.
Hypothesis Hv : valid_input cs.
Hypothesis Hr : repr (A := array uint) c cs.

Lemma Hn : (φ (PArray.length c)) = Z.of_N (len cs).
Proof.
  destruct Hr as [Hl _]. unfold len. rewrite nat_N_Z. symmetry. exact Hl.
Qed.

Lemma len_bounds : (2 <= len cs <= 100)%N.
Proof. destruct Hv as [H _ _ _]. exact H. Qed.

Lemma cget : forall i : int, ((φ i) < Z.of_N (len cs))%Z ->
  val c.[i] = coin cs (val i).
Proof.
  intros i Hi. destruct Hr as [Hl Hc].
  assert (Hi' : (Z.to_nat (φ i) < List.length cs)%nat) by (unfold len in Hi; lia).
  destruct (Hc _ Hi') as (m & Hm & Hrm).
  unfold repr, repr_uint in Hrm.
  rewrite Z2Nat.id in Hrm by (pose proof (to_Z_bounded i); lia).
  rewrite of_to_Z in Hrm.
  unfold val, coin. rewrite Z_N_nat. rewrite (nth_error_nth cs _ 0%N Hm).
  exact Hrm.
Qed.

Lemma bound_val : val (bound c) = (cmax cs + cmax1 cs)%N /\
                  ((φ (bound c)) <= 2000000)%Z.
Proof.
  pose proof Hn as Hn'. pose proof len_bounds as Hl.
  pose proof (cget (PArray.length c - 1) ltac:(sia)) as E1.
  pose proof (cget (PArray.length c - 2) ltac:(sia)) as E2.
  assert (V1 : val (PArray.length c - 1) = (len cs - 1)%N) by (unfold val; sia).
  assert (V2 : val (PArray.length c - 2) = (len cs - 2)%N) by (unfold val; sia).
  rewrite V1 in E1. rewrite V2 in E2.
  pose proof (coin_max cs Hv (len cs - 1) ltac:(lia)) as M1.
  pose proof (coin_max cs Hv (len cs - 2) ltac:(lia)) as M2.
  unfold bound, cmax, cmax1. cbv zeta.
  rewrite <- E1, <- E2 in *. unfold val in *. split; sia.
Qed.

Definition Kinv (x k : int) : Prop :=
  (val k < len cs)%N /\ (coin cs (val k) <= val x)%N /\
  ((val k + 1 < len cs)%N -> (val x <= coin cs (val k + 1))%N).

Definition Kpost (x k : int) : Prop :=
  (val k < len cs)%N /\ (coin cs (val k) <= val x)%N /\
  ((val k + 1 < len cs)%N -> (val x < coin cs (val k + 1))%N).

Lemma kupd_spec : forall x k, Kinv x k -> Kpost x (kupd c (PArray.length c) x k).
Proof.
  intros x k (Hk & Hkx & Hnext). pose proof Hn as Hn'. pose proof len_bounds as Hl.
  unfold kupd.
  assert (Hk1 : val (k + 1) = (val k + 1)%N) by (unfold val in *; sia).
  destruct (k + 1 <? PArray.length c) eqn:E1.
  - rewrite ltb_spec in E1.
    assert (Hc1 : val c.[k + 1] = coin cs (val k + 1)).
    { rewrite <- Hk1. apply cget. lia. }
    destruct (c.[k + 1] <=? x) eqn:E2.
    + rewrite leb_spec in E2.
      assert (Hle : (coin cs (val k + 1) <= val x)%N)
        by (rewrite <- Hc1; unfold val; lia).
      unfold Kpost. rewrite Hk1. split; [unfold val in *; lia|]. split; [exact Hle|].
      intros H2. pose proof (coin_lt cs Hv (val k + 1) (val k + 1 + 1) ltac:(lia) H2).
      assert (Hkn : (val k + 1 < len cs)%N) by lia.
      specialize (Hnext Hkn). lia.
    + rewrite <- Bool.not_true_iff_false, leb_spec in E2.
      unfold Kpost. split; [exact Hk|]. split; [exact Hkx|].
      intros _. rewrite <- Hc1. unfold val. lia.
  - unfold Kpost. split; [exact Hk|]. split; [exact Hkx|].
    intros H2. rewrite <- Bool.not_true_iff_false, ltb_spec in E1.
    exfalso. unfold val in *. lia.
Qed.

Lemma kpost_below : forall x k, Kpost x k ->
  forall i, (i < len cs)%N -> (coin cs i <= val x)%N -> (i <= val k)%N.
Proof.
  intros x k (Hk & Hkx & Hnext) i Hi Hix.
  destruct (N.le_gt_cases i (val k)) as [Hik | Hik]; [exact Hik|].
  exfalso. specialize (Hnext ltac:(lia)).
  pose proof (coin_le cs Hv (val k + 1) i ltac:(lia) Hi). lia.
Qed.

Lemma kpost_largest : forall x k, Kpost x k ->
  largest_le cs (val x) (coin cs (val k)).
Proof.
  intros x k HK. pose proof HK as (Hk & Hkx & Hnext).
  split; [apply coin_in; exact Hk|]. split; [exact Hkx|].
  intros e He Hex. destruct (in_coin cs e He) as [i [Hi <-]].
  apply coin_le; [exact Hv | | exact Hk].
  apply (kpost_below x k HK i Hi Hex).
Qed.

Definition Inv (x : int) (t g : array int) : Prop :=
  PArray.length t = bound c /\ PArray.length g = bound c /\
  forall y : N, (y < val x)%N ->
    min_coins cs y (tv t y) /\ greedy_uses cs y (tv g y) /\ (tv g y <= tv t y)%N.

Lemma minloop_spec : forall (t : array int) (x hi : int),
  ((φ hi) <= Z.of_N (len cs))%Z ->
  (forall i, (i < val hi)%N -> (coin cs i <= val x)%N) ->
  forall z j acc H, gap hi j = z -> ((φ j) <= (φ hi))%Z ->
  (exists i, (i < val j)%N /\ val acc = tv t (val x - coin cs i)%N) ->
  (forall i, (i < val j)%N -> (val acc <= tv t (val x - coin cs i))%N) ->
  (exists i, (i < val hi)%N /\
     val (minloop c t x hi j acc H) = tv t (val x - coin cs i)%N) /\
  (forall i, (i < val hi)%N ->
     (val (minloop c t x hi j acc H) <= tv t (val x - coin cs i))%N).
Proof.
  intros t x hi Hhi Hcx z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j acc H Hz Hjh Hex Hall.
  rewrite minloop_eq.
  destruct (bdec (j <? hi)) as [Hj | Hj].
  - pose proof Hj as Hj'. rewrite ltb_spec in Hj'.
    assert (Hj1 : val (j + 1) = (val j + 1)%N) by (unfold val; sia).
    assert (Hcj : val c.[j] = coin cs (val j)) by (apply cget; lia).
    assert (Hcjx : (coin cs (val j) <= val x)%N) by (apply Hcx; unfold val; lia).
    assert (Hidx : x - c.[j] = ix (val x - coin cs (val j))).
    { apply ix_eq. rewrite <- Hcj in *. unfold val in *. sia. }
    cbv zeta. rewrite Hidx.
    set (v := t.[ix (val x - coin cs (val j))]).
    assert (Hvv : val v = tv t (val x - coin cs (val j))) by reflexivity.
    destruct (v <? acc) eqn:E.
    + rewrite ltb_spec in E.
      eapply IH; [rewrite <- Hz; apply dec_step; exact Hj | reflexivity | sia | | ].
      * exists (val j). rewrite Hj1. split; [lia | exact Hvv].
      * intros i Hi. rewrite Hj1 in Hi.
        destruct (N.eq_dec i (val j)) as [-> | Ne]; [rewrite Hvv; lia|].
        specialize (Hall i ltac:(lia)). unfold val in *. lia.
    + rewrite <- Bool.not_true_iff_false, ltb_spec in E.
      eapply IH; [rewrite <- Hz; apply dec_step; exact Hj | reflexivity | sia | | ].
      * destruct Hex as [i [Hi Hie]]. exists i. rewrite Hj1. split; [lia | exact Hie].
      * intros i Hi. rewrite Hj1 in Hi.
        destruct (N.eq_dec i (val j)) as [-> | Ne];
          [rewrite <- Hvv; unfold val; lia|].
        apply Hall. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hj.
    assert (j = hi) by (apply to_Z_inj; lia). subst j.
    split; assumption.
Qed.

Lemma outer_spec : forall z x k t g H,
  gap (bound c) x = z ->
  (1 <= (φ x))%Z -> ((φ x) <= (φ (bound c)))%Z ->
  Kinv x k -> Inv x t g ->
  (outer c (PArray.length c) (bound c) x k t g H = true ->
     forall y, (y < val (bound c))%N -> gopt cs y) /\
  (outer c (PArray.length c) (bound c) x k t g H = false ->
     exists y, counterexample cs y).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros x k t g H Hz Hx1 HxB HK [Hlt [Hlg Hinv]].
  pose proof Hn as Hn'. pose proof len_bounds as Hlb.
  destruct bound_val as [HBv HBb].
  rewrite outer_eq.
  destruct (bdec (x <? bound c)) as [Hx | Hx].
  - pose proof Hx as Hx'. rewrite ltb_spec in Hx'.
    cbv zeta.
    pose proof (kupd_spec x k HK) as HK'.
    set (k' := kupd c (PArray.length c) x k) in *.
    pose proof HK' as [Hk'n [Hk'x Hk'next]].
    assert (Hvx : (0 < val x)%N) by (unfold val; lia).
    pose proof (kpost_largest x k' HK') as Hlarg.
    assert (Hck : val c.[k'] = coin cs (val k')) by (apply cget; unfold val in Hk'n; lia).
    pose proof (coin_pos cs Hv (coin cs (val k')) (coin_in cs (val k') Hk'n)) as Hckpos.
    assert (Hidx : x - c.[k'] = ix (val x - coin cs (val k'))).
    { apply ix_eq. rewrite <- Hck in *. unfold val in *. sia. }
    rewrite Hidx.
    destruct (Hinv (val x - coin cs (val k'))%N ltac:(lia)) as [_ [Hgy _]].
    pose proof (sums_le cs Hv _ _ (greedy_sums cs _ _ Hgy)) as Hgyb.
    unfold tv in Hgy, Hgyb.
    set (gv := g.[ix (val x - coin cs (val k'))]) in *.
    assert (Hgx : val (gv + 1) = (val gv + 1)%N)
      by (clear -Hgyb Hx' HBb; unfold val in *; sia).
    assert (Hgreedy : greedy_uses cs (val x) (val (gv + 1))).
    { rewrite Hgx. apply (greedy_step cs (val x) (coin cs (val k')) (val gv)); [lia | exact Hlarg | exact Hgy]. }
    assert (Hk1v : val (k' + 1) = (val k' + 1)%N)
      by (clear -Hk'n Hlb; unfold val in *; sia).
    assert (Hcoinhi : forall i, (i < val (k' + 1))%N -> (coin cs i <= val x)%N).
    { intros i Hi. rewrite Hk1v in Hi.
      pose proof (coin_le cs Hv i (val k') ltac:(lia) Hk'n). lia. }
    assert (Hx1i : x - 1 = ix (val x - coin cs 0)%N).
    { apply ix_eq. rewrite (vi_first _ Hv). unfold val. sia. }
    rewrite Hx1i.
    assert (Hv1 : val 1 = 1%N) by reflexivity.
    destruct (minloop_spec t x (k' + 1) ltac:(unfold val in Hk'n; sia) Hcoinhi
                _ 1 (t.[ix (val x - coin cs 0)])
                (Zwf_well_founded 0 (gap (k' + 1) 1)) eq_refl
                ltac:(change (φ 1) with 1%Z; unfold val in Hk'n; sia))
      as [Hmex Hmall].
    { exists 0%N. rewrite Hv1. split; [lia | reflexivity]. }
    { intros i Hi. rewrite Hv1 in Hi. replace i with 0%N by lia. unfold tv. lia. }
    set (r := minloop c t x (k' + 1) 1 t.[ix (val x - coin cs 0)]
                (Zwf_well_founded 0 (gap (k' + 1) 1))) in *.
    destruct Hmex as [i0 [Hi0 Hri0]].
    rewrite Hk1v in Hi0.
    assert (Hmin : min_coins cs (val x) (val r + 1)).
    { apply (min_step cs Hv (tv t) (val x) (val r) (coin cs i0)).
      - exact Hvx.
      - apply coin_in. lia.
      - apply Hcoinhi. rewrite Hk1v. exact Hi0.
      - intros y Hy. apply (Hinv y Hy).
      - symmetry. exact Hri0.
      - intros d Hd Hdx. destruct (in_coin cs d Hd) as [i [Hi <-]].
        apply Hmall. rewrite Hk1v.
        pose proof (kpost_below x k' HK' i Hi Hdx). lia. }
    pose proof (sums_le cs Hv _ _ (proj1 Hmin)) as Hrb.
    assert (Hr1 : val (r + 1) = (val r + 1)%N)
      by (clear -Hrb Hx' HBb; unfold val in *; sia).
    destruct (r + 1 <? gv + 1) eqn:Ec.
    + split; [discriminate|]. intros _. exists (val x). split; [exact Hvx|].
      exists (val (r + 1)), (val (gv + 1)).
      split; [rewrite Hr1; exact Hmin|]. split; [exact Hgreedy|].
      rewrite ltb_spec in Ec. unfold val. lia.
    + rewrite <- Bool.not_true_iff_false, ltb_spec in Ec.
      assert (Hx1v : val (x + 1) = (val x + 1)%N)
        by (clear -Hx' HBb; unfold val in *; sia).
      eapply IH; [rewrite <- Hz; apply dec_step; exact Hx | reflexivity | sia | sia | | ].
      * destruct HK' as (A1 & A2 & A3). unfold Kinv. rewrite Hx1v.
        split; [exact A1|]. split; [lia|]. intros A4. specialize (A3 A4). lia.
      * split; [rewrite alength_set; exact Hlt|].
        split; [rewrite alength_set; exact Hlg|].
        intros y Hy. rewrite Hx1v in Hy.
        rewrite (tv_set t x _ y)
          by (clear -Hy Hlt Hx' HBb; rewrite ?Hlt, ?wB_val; unfold val in *; lia).
        rewrite (tv_set g x _ y)
          by (clear -Hy Hlg Hx' HBb; rewrite ?Hlg, ?wB_val; unfold val in *; lia).
        destruct (N.eqb_spec y (val x)) as [-> | Ne].
        -- split; [rewrite Hr1; exact Hmin|]. split; [exact Hgreedy|].
           clear -Ec. unfold val. lia.
        -- apply Hinv. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hx.
    split; [|discriminate].
    intros _ y Hy m g0 Hs Hg0.
    destruct (Hinv y ltac:(clear -Hy Hx HxB; unfold val in *; lia)) as [[_ Hm] [Hgy Hle]].
    rewrite (greedy_fun cs y g0 Hg0 _ Hgy).
    specialize (Hm m Hs). lia.
Qed.

Lemma run_spec :
  (run c = true -> forall y, (y < cmax cs + cmax1 cs)%N -> gopt cs y) /\
  (run c = false -> exists y, counterexample cs y).
Proof.
  pose proof Hn as Hn'. pose proof len_bounds as Hlb.
  destruct bound_val as [HBv HBb].
  assert (HBm : PArray.length (PArray.make (bound c) 0) = bound c).
  { rewrite alength_make.
    replace (bound c <=? max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  assert (HK0 : Kinv 1 0).
  { unfold Kinv. change (val 0) with 0%N. change (val 1) with 1%N.
    rewrite (vi_first _ Hv). split; [lia|]. split; [lia|].
    change (0 + 1)%N with 1%N. intros H1. pose proof (coin_lt cs Hv 0 1 ltac:(lia) H1) as H2.
    rewrite (vi_first _ Hv) in H2. lia. }
  assert (HI0 : Inv 1 (PArray.make (bound c) 0) (PArray.make (bound c) 0)).
  { split; [exact HBm|]. split; [exact HBm|].
    intros y Hy. change (val 1) with 1%N in Hy. replace y with 0%N by lia.
    rewrite !tv_make. change (val 0) with 0%N.
    split; [split; [constructor | intros; lia]|]. split; [constructor | lia]. }
  pose proof (cmax_pos cs Hv) as Hcp.
  unfold run. cbv zeta.
  destruct (outer_spec _ 1 0 _ _ (Zwf_well_founded 0 (gap (bound c) 1)) eq_refl
              ltac:(change (φ 1) with 1%Z; lia)
              ltac:(change (φ 1) with 1%Z; unfold val in HBv; lia) HK0 HI0) as [HT HF].
  split; [|exact HF].
  intros E y Hy. apply (HT E). rewrite HBv. exact Hy.
Qed.

Lemma bool_match_of_iff : forall (b : bool) (P : Prop),
  (b = true <-> P) -> match b with true => P | false => ~ P end.
Proof.
  intros [|] P [H1 H2]; [exact (H1 eq_refl)|intros HP; discriminate (H2 HP)].
Qed.

Lemma run_correct : exists b : bool, repr (run c) b /\ canonical_spec cs b.
Proof.
  exists (run c). split; [reflexivity|].
  destruct run_spec as [HT HF]. unfold canonical_spec.
  destruct (run c) eqn:E.
  - split; [intros _ | reflexivity].
    apply (no_counterexample cs Hv). exact (HT eq_refl).
  - split; [discriminate|]. intros Hno.
    destruct (HF eq_refl) as [y Hy]. exfalso. exact (Hno y Hy).
Qed.

End Machine.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition canonical : array uint -> bool := canonical_impl.
Elpi complexity canonical.

Definition canonical_correct : forall (c : list N) (x : array uint),
  valid_input c -> repr x c ->
  exists b : bool, repr (canonical x) b /\ canonical_spec c b
  := fun c x Hv Hr => run_correct c x Hv Hr.

(* ------------------------------------------------------------------ *)
(* Cost                                                                *)
(* ------------------------------------------------------------------ *)

(* canonical_time.  The cost translations ([Elpi complexity], next to each
   definition, callee first): sumbool, bdec, minloop, kupd, outer, bound,
   run, canonical_impl, canonical.  Loop lemmas (induction on a nat bound
   of the Acc measure gap):
   - minloop from j: at most 50 * gap hi j + 10 steps;
   - kupd, bound: at most 30 steps each;
   - outer from x, with the pointer k below n: at most
     (50 * n + 200) * gap B x + 10 (each amount: kupd, one minloop over
     k' + 1 <= n coins, two reads, two writes);
   - run: that with x = 1, k = 0, plus 100.
   Then gap B 1 <= c_n + c_(n-1) <= 2 * max_size (valid_input gives
   n >= 2, so the two reads are in bounds), whence c1 = 400, c2 = 200. *)

Lemma bdec_time b (w : bool_cost stepsCM b) : (cost (bdec_cost stepsCM b w) <= 2)%nat.
Proof. destruct w; cbn; lia. Qed.

Lemma minloop_time c cC t tC x xC hi hiC j jC acc accC H HC :
  (cost (extract (extract (extract (extract (extract (extract (minloop_cost stepsCM c cC) t tC) x xC) hi hiC) j jC) acc accC) H HC)
     <= 50 * Z.to_nat (gap hi j) + 10)%nat.
Proof.
  unfold minloop_cost. cbn.
  match goal with |- context [@cost ?T (?G c cC t tC x xC hi hiC j jC acc accC H HC)] =>
    assert (HG : forall k j jC acc accC H HC, (Z.to_nat (gap hi j) <= k)%nat ->
       (cost (G c cC t tC x xC hi hiC j jC acc accC H HC) <= 50 * k + 10)%nat) end.
  { induction k as [|k IH]; intros j' jC' acc' accC' [g] HC' Hk;
      cost_simpl;
      pose proof (bdec_time (j' <? hi) (bool_w (j' <? hi))) as HB;
      cost_destruct (bdec (j' <? hi)); cost_simpl.
    - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e). unfold gap in Hk. lia.
    - lia.
    - pose proof (proj1 (Uint63.ltb_spec _ _) e) as Hlt.
      assert (Hk' : (Z.to_nat (gap hi (j' + 1)) <= k)%nat).
      { unfold gap in *. assert (φ (j' + 1) = φ j' + 1)%Z by (zify; Z.to_euclidean_division_equations; lia). lia. }
      cost_destruct (t.[x - c.[j']] <? acc'); cost_simpl;
      match goal with |- context [@cost ?T (?G' c cC t tC x xC hi hiC (j' + 1)%uint63 ?w ?a ?wa ?h ?e)] =>
          pose proof (IH (j' + 1)%uint63 w a wa h e Hk' : (@cost T (G' c cC t tC x xC hi hiC (j' + 1)%uint63 w a wa h e) <= _)%nat) as HI end;
      lia.
    - lia. }
  match goal with |- context [@cost ?T (?G c cC t tC x xC hi hiC j jC acc accC H HC)] =>
    exact (HG _ j jC acc accC H HC (le_n _) : (@cost T (G c cC t tC x xC hi hiC j jC acc accC H HC) <= _)%nat) end.
Qed.

Lemma kupd_time c cC n nC x xC k kC :
  (cost (extract (extract (extract (kupd_cost stepsCM c cC) n nC) x xC) k kC) <= 30)%nat.
Proof.
  unfold kupd_cost. cost_simpl.
  cost_destruct (k + 1 <? n); cost_simpl; [cost_destruct (c.[k + 1] <=? x); cost_simpl|]; lia.
Qed.

Lemma bound_time c cC :
  (cost (bound_cost stepsCM c cC) <= 30)%nat.
Proof.
  unfold bound_cost. cost_simpl. lia.
Qed.

Ltac z0 f := repeat match goal with |- context [cost (f ?a ?b ?c)] => change (cost (f a b c)) with 0%nat end.
Ltac z1 f := repeat match goal with |- context [cost (extract (f ?a ?b ?c) ?d ?e)] =>
  change (cost (extract (f a b c) d e)) with 0%nat end.
Ltac z2 f := repeat match goal with |- context [cost (extract (extract (f ?a ?b ?c) ?d ?e) ?d1 ?e1)] =>
  change (cost (extract (extract (f a b c) d e) d1 e1)) with 0%nat end.
Ltac z3 f := repeat match goal with |- context [cost (extract (extract (extract (f ?a ?b ?c) ?d ?e) ?d1 ?e1) ?d2 ?e2)] =>
  change (cost (extract (extract (extract (f a b c) d e) d1 e1) d2 e2)) with 0%nat end.
Ltac z4 f := repeat match goal with |- context [cost (extract (extract (extract (extract (f ?a ?b ?c) ?d ?e) ?d1 ?e1) ?d2 ?e2) ?d3 ?e3)] =>
  change (cost (extract (extract (extract (extract (f a b c) d e) d1 e1) d2 e2) d3 e3)) with 0%nat end.
Ltac z5 f := repeat match goal with |- context [cost (extract (extract (extract (extract (extract (f ?a ?b ?c) ?d ?e) ?d1 ?e1) ?d2 ?e2) ?d3 ?e3) ?d4 ?e4)] =>
  change (cost (extract (extract (extract (extract (extract (f a b c) d e) d1 e1) d2 e2) d3 e3) d4 e4)) with 0%nat end.
Ltac z6 f := repeat match goal with |- context [cost (extract (extract (extract (extract (extract (extract (f ?a ?b ?c) ?d ?e) ?d1 ?e1) ?d2 ?e2) ?d3 ?e3) ?d4 ?e4) ?d5 ?e5)] =>
  change (cost (extract (extract (extract (extract (extract (extract (f a b c) d e) d1 e1) d2 e2) d3 e3) d4 e4) d5 e5)) with 0%nat end.
Ltac z7 f := repeat match goal with |- context [cost (extract (extract (extract (extract (extract (extract (extract (f ?a ?b ?c) ?d ?e) ?d1 ?e1) ?d2 ?e2) ?d3 ?e3) ?d4 ?e4) ?d5 ?e5) ?d6 ?e6)] =>
  change (cost (extract (extract (extract (extract (extract (extract (extract (f a b c) d e) d1 e1) d2 e2) d3 e3) d4 e4) d5 e5) d6 e6)) with 0%nat end.

Ltac gen_minloop := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (extract (extract (minloop_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC) ?g ?gC =>
    let Hc := fresh "Hmin" in
    pose proof (minloop_time a aC b bC c cC d dC e eC f fC g gC : (@cost T X <= _)%nat) as Hc;
    revert Hc; generalize (@cost T X); intros ? Hc end end.
Ltac gen_kupd := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (kupd_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC =>
    let Hc := fresh "Hkupd" in
    pose proof (kupd_time a aC b bC c cC d dC : (@cost T X <= _)%nat) as Hc;
    revert Hc; generalize (@cost T X); intros ? Hc end end.

Lemma kupd_lt c n x k : (φ k < φ n)%Z -> (φ (kupd c n x k) < φ n)%Z.
Proof.
  intros H. unfold kupd.
  destruct (k + 1 <? n) eqn:E; [|exact H].
  rewrite Uint63.ltb_spec in E.
  destruct (c.[k + 1] <=? x); [exact E|exact H].
Qed.

Ltac set_simpl :=
  repeat match goal with
  | |- context [cost (extract (extract (extract (set_cost ?a ?b ?c) ?d ?e) ?f ?g) ?h ?i)] =>
      change (cost (extract (extract (extract (set_cost a b c) d e) f g) h i)) with 1%nat
  | |- context [cost (extract (extract (set_cost ?a ?b ?c) ?d ?e) ?f ?g)] =>
      change (cost (extract (extract (set_cost a b c) d e) f g)) with 0%nat
  | |- context [cost (extract (set_cost ?a ?b ?c) ?d ?e)] =>
      change (cost (extract (set_cost a b c) d e)) with 0%nat
  | |- context [cost (set_cost ?a ?b ?c)] =>
      change (cost (set_cost a b c)) with 0%nat
  end.

Lemma gap_k1 k n : (φ k < φ n)%Z -> (Z.to_nat (gap (k + 1) 1) <= Z.to_nat (φ n))%nat.
Proof.
  intros H. pose proof (to_Z_bounded n). pose proof (to_Z_bounded k).
  assert (E : φ (k + 1) = (φ k + 1)%Z) by (zify; Z.to_euclidean_division_equations; lia).
  unfold gap. rewrite E. change (φ 1) with 1%Z. lia.
Qed.

Lemma outer_time c cC n nC B BC x xC k kC t tC g gC H HC :
  (φ k < φ n)%Z ->
  (cost (extract (extract (extract (extract (extract (extract (extract (outer_cost stepsCM c cC) n nC) B BC) x xC) k kC) t tC) g gC) H HC)
     <= (50 * Z.to_nat (φ n) + 200) * Z.to_nat (gap B x) + 10)%nat.
Proof.
  intros Hkn.
  remember (50 * Z.to_nat (φ n) + 200)%nat as A eqn:EA.
  unfold outer_cost. cbn.
  match goal with |- context [@cost ?T (?G c cC n nC B BC x xC k kC t tC g gC H HC)] =>
    assert (HG : forall m x xC k kC t tC g gC H HC, (Z.to_nat (gap B x) <= m)%nat -> (φ k < φ n)%Z ->
       (cost (G c cC n nC B BC x xC k kC t tC g gC H HC) <= A * m + 10)%nat) end.
  { induction m as [|m IH]; intros x' xC' k' kC' t' tC' g' gC' [h] HC' Hm Hk;
      cost_simpl;
      pose proof (bdec_time (x' <? B) (bool_w (x' <? B))) as HB;
      cost_destruct (bdec (x' <? B)); cost_simpl.
    - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e). unfold gap in Hm. lia.
    - lia.
    - z0 kupd_cost; z1 kupd_cost; z2 kupd_cost.
      z0 minloop_cost; z1 minloop_cost; z2 minloop_cost; z3 minloop_cost; z4 minloop_cost; z5 minloop_cost.
      gen_kupd. gen_minloop.
      pose proof (gap_k1 (kupd c n x' k') n (kupd_lt c n x' k' Hk)) as Hgk.
      pose proof (kupd_lt c n x' k' Hk) as Hk'.
      pose proof (proj1 (Uint63.ltb_spec _ _) e) as Hlt.
      assert (Hm' : (Z.to_nat (gap B (x' + 1)) <= m)%nat).
      { unfold gap in *. assert (φ (x' + 1) = φ x' + 1)%Z by (zify; Z.to_euclidean_division_equations; lia). lia. }
      cost_destruct (minloop c t' x' (kupd c n x' k' + 1) 1 t'.[x' - 1] (Zwf_well_founded 0 (gap (kupd c n x' k' + 1) 1)) + 1 <? g'.[x' - c.[kupd c n x' k']] + 1); cost_simpl.
      + nia.
      + set_simpl.
        z0 outer_cost; z1 outer_cost; z2 outer_cost; z3 outer_cost; z4 outer_cost; z5 outer_cost; z6 outer_cost; z7 outer_cost.
        match goal with |- context [@cost ?T (?G' c cC n nC B BC (x' + 1)%uint63 ?w ?kk ?kw ?tt ?tw ?gg ?gw ?hh ?ee)] =>
          pose proof (IH (x' + 1)%uint63 w kk kw tt tw gg gw hh ee Hm' Hk' : (@cost T (G' c cC n nC B BC (x' + 1)%uint63 w kk kw tt tw gg gw hh ee) <= _)%nat) as HI end.
        lia.
    - lia. }
  match goal with |- context [@cost ?T (?G c cC n nC B BC x xC k kC t tC g gC H HC)] =>
    exact (HG _ x xC k kC t tC g gC H HC (le_n _) Hkn : (@cost T (G c cC n nC B BC x xC k kC t tC g gC H HC) <= _)%nat) end.
Qed.

Ltac gen_outer := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (extract (extract (extract (outer_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC) ?g ?gC) ?h ?hC =>
    let Hc := fresh "Houter" in
    pose proof (outer_time a aC b bC c cC d dC e eC f fC g gC h hC ltac:(assumption) : (@cost T X <= _)%nat) as Hc;
    revert Hc; generalize (@cost T X); intros ? Hc end end.
Ltac gen_bound := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with bound_cost stepsCM ?a ?aC =>
    let Hc := fresh "Hbound" in
    pose proof (bound_time a aC : (@cost T X <= _)%nat) as Hc;
    revert Hc; generalize (@cost T X); intros ? Hc end end.

Lemma run_time c cC :
  (φ 0 < φ (PArray.length c))%Z ->
  (cost (run_cost stepsCM c cC) <= (50 * Z.to_nat (φ (PArray.length c)) + 200) * Z.to_nat (gap (bound c) 1) + 100)%nat.
Proof.
  intros Hn.
  match goal with |- (_ <= ?r)%nat => remember r as R eqn:ER end.
  unfold run_cost. cost_simpl.
  gen_bound.
  z0 outer_cost; z1 outer_cost; z2 outer_cost; z3 outer_cost; z4 outer_cost; z5 outer_cost; z6 outer_cost; z7 outer_cost.
  gen_outer.
  z0 make_cost. z1 make_cost.
  repeat match goal with
  | |- context [cost (extract (extract (make_cost ?a ?b ?c) ?d ?e) ?f ?g)] =>
      change (cost (extract (extract (make_cost a b c) d e) f g)) with 1%nat
  end.
  subst R. change (c.[PArray.length c - 1] + c.[PArray.length c - 2]) with (bound c) in *.
  match type of Houter with context [Z.to_nat (φ ?L)] => match goal with |- context [Z.to_nat (φ ?L2)] => assert (EL : Z.to_nat (φ L) = Z.to_nat (φ L2)) by reflexivity; rewrite EL in Houter end end.
  clear EL. match goal with |- (_ <= ?P + 100)%nat => revert Houter; generalize P end. intros; lia.
Qed.

Ltac bridge H :=
  repeat match type of H with context [@PArray.length ?A ?L] =>
    match goal with |- context [@PArray.length ?A2 ?L2] =>
      assert_fails (constr_eq_strict (@PArray.length A L) (@PArray.length A2 L2));
      let EL := fresh "EL" in
      assert (EL : @PArray.length A L = @PArray.length A2 L2) by reflexivity; rewrite EL in H; clear EL end end.

Lemma canonical_impl_time c cC :
  (φ 0 < φ (PArray.length c))%Z ->
  (cost (canonical_impl_cost stepsCM c cC) <= (50 * Z.to_nat (φ (PArray.length c)) + 200) * Z.to_nat (gap (bound c) 1) + 110)%nat.
Proof.
  intros Hn.
  match goal with |- (_ <= ?r)%nat => remember r as R eqn:ER end.
  unfold canonical_impl_cost. cost_simpl.
  pose proof (run_time c cC Hn) as Hr. subst R.
  change (@PArray.length int c) with (@PArray.length repr.uint c) in Hr. lia.
Qed.

Lemma canonical_cost_time c cC :
  (φ 0 < φ (PArray.length c))%Z ->
  (cost (canonical_cost stepsCM c cC) <= (50 * Z.to_nat (φ (PArray.length c)) + 200) * Z.to_nat (gap (bound c) 1) + 110)%nat.
Proof. intros Hn. exact (canonical_impl_time c cC Hn). Qed.

Lemma fold_max (f : nat -> nat) : forall l a,
  (a <= List.fold_left (fun acc i => Nat.max acc (f i)) l a)%nat /\
  (forall i, In i l -> f i <= List.fold_left (fun acc i => Nat.max acc (f i)) l a)%nat.
Proof.
  induction l as [|y l IH]; intros a; cbn.
  - split; [lia | intros i []].
  - destruct (IH (Nat.max a (f y))) as [H1 H2]. split; [lia|].
    intros i [<- | Hi]; [lia | apply H2, Hi].
Qed.

Lemma size_le_max (x : array uint) (i : int) :
  (φ i < φ (PArray.length x))%Z -> (Z.to_nat (φ x.[i]) <= max_size x)%nat.
Proof.
  intros Hi. unfold max_size.
  destruct (fold_max (fun i0 => size x.[of_Z (Z.of_nat i0)]) (List.seq 0 (size x)) 0%nat) as [_ H2].
  pose proof (to_Z_bounded i).
  specialize (H2 (Z.to_nat (φ i))). rewrite (Z2Nat.id _ (proj1 (to_Z_bounded i))) in H2. rewrite of_to_Z in H2.
  apply H2. apply in_seq. unfold size, size_array. lia.
Qed.

Lemma size_le_max' (x : array int) (i : int) :
  (φ i < φ (PArray.length x))%Z -> (Z.to_nat (φ x.[i]) <= @max_size uint size_uint x)%nat.
Proof. exact (size_le_max x i). Qed.

Lemma arith2 (a b : Z) (M : nat) : (0 <= a)%Z -> (0 <= b)%Z ->
  (Z.to_nat a <= M)%nat -> (Z.to_nat b <= M)%nat ->
  (Z.to_nat ((a + b) mod wB - φ 1) <= 2 * M)%nat.
Proof.
  intros Ha Hb H1 H2. change (φ 1) with 1%Z.
  pose proof (Z.mod_le (a + b) wB ltac:(lia) ltac:(rewrite wB_val; lia)). lia.
Qed.

Lemma idx_lt (y : array int) (d : int) : (φ d <= 2)%Z -> (1 <= φ d)%Z -> (2 <= φ (PArray.length y))%Z ->
  (φ (PArray.length y - d) < φ (PArray.length y))%Z.
Proof. intros. zify; Z.to_euclidean_division_equations; lia. Qed.

Lemma bound_le (x : array uint) : (2 <= φ (PArray.length x))%Z ->
  (Z.to_nat (gap (bound x) 1) <= 2 * max_size x)%nat.
Proof.
  intros H. unfold gap, bound. cbv zeta. rewrite add_spec.
  apply arith2; [apply to_Z_bounded | apply to_Z_bounded | |];
    apply size_le_max'; apply idx_lt; try exact H; (change (φ 1) with 1%Z || change (φ 2) with 2%Z); lia.
Qed.
Lemma two_le (y : array int) (l : N) : φ (PArray.length y) = Z.of_N l -> (2 <= l)%N ->
  (2 <= φ (PArray.length y))%Z.
Proof. intros. lia. Qed.

Lemma arith_final (n G M : nat) : (G <= 2 * M)%nat ->
  ((50 * n + 200) * G + 110 <= 400 * ((n + 1) * (M + 1)) + 200)%nat.
Proof. intros H. nia. Qed.

Theorem canonical_time : exists c1 c2 : nat,
  forall (denominations : list N)
  (denominations_arr : array uint),
  valid_input denominations
  -> repr denominations_arr denominations ->
  (cost1 canonical_cost denominations_arr <= c1 * ((size denominations_arr + 1) * (max_size denominations_arr + 1)) + c2)%nat.
Proof.
  exists 400%nat, 200%nat. intros cs x Hv Hr.
  pose proof (Hn cs x Hr) as E. pose proof (len_bounds cs Hv) as L.
  assert (H2 : (2 <= φ (PArray.length x))%Z) by (eapply two_le; [exact E | lia]).
  assert (H0 : (φ 0 < φ (PArray.length x))%Z) by (change (φ 0) with 0%Z; eapply Z.lt_le_trans; [|exact H2]; lia).
  pose proof (bound_le x H2) as HB.
  pose proof (canonical_cost_time x (witness x) H0) as HC.
  unfold cost1. eapply Nat.le_trans; [exact HC|].
  apply arith_final. exact HB.
Qed.
