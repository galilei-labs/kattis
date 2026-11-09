(* Correctness proofs for canonical_implem.v. *)
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
Import ListNotations.

Unset Lia Cache.

From Canonical Require Export canonical_implem.



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
  destruct run_spec as [HT HF]. unfold canonical_spec. apply bool_match_of_iff.
  destruct (run c) eqn:E.
  - split; [intros _ | reflexivity].
    apply (no_counterexample cs Hv). exact (HT eq_refl).
  - split; [discriminate|]. intros Hno.
    destruct (HF eq_refl) as [y Hy]. exfalso. exact (Hno y Hy).
Qed.

End Machine.

Definition canonical_correct : forall (c : list N) (x : array uint),
  valid_input c -> repr x c ->
  exists b : bool, repr (canonical x) b /\ canonical_spec c b
  := fun c x Hv Hr => run_correct c x Hv Hr.
