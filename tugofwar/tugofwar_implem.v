(* Implementation of tugofwar (tugofwar.spec): subset-sum dynamic
   programming with a team-size dimension.

   Code.  [tugofwar a] computes the total weight S (one pass), then fills a
   flat boolean table of (K+1) rows of W cells, K = n - n/2 (the larger
   balanced team size) and W = S/2 + 1: cell c*W + s says that some set of
   exactly c of the people processed so far weighs exactly s.  The people
   are processed one by one (from the last to the first); for a person of
   weight x, the rows are updated from c = K down to 1, and in row c the
   cells s = x .. W-1 receive  cell(c-1, s-x)  (an or): since the rows go
   downwards, row c-1 still holds the previous person's values, so the
   update is in place.  The answer is the largest s <= S/2 reachable with
   n/2 or n - n/2 people: (s, S - s).

   Proof.  [reachZ l c s]: some choice of people of l has c people and
   weight s.  The table invariant [Tbl] says each cell is reachZ of the
   suffix of the people processed so far; [reach_cons] is the recurrence.
   A division of the people with balanced team sizes has a team of n/2 or
   n - n/2 people; either that team or the other weighs at most S/2, which
   gives optimality of the largest reachable s <= S/2.

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) _] proof (the template's device).  No nat, no Z, no list in
   the code.

   Cost.  [Elpi complexity] translates sumbool, bdec, orb, the five loops,
   tugofwar_impl and tugofwar (callee first).  Loop bounds: sum_loop
   50 i + 10, cell_loop 50 (W - s) + 10, row_loop (50 W + 50) c + 10,
   item_loop ((50 W + 50) K + 60) i + 10, best_loop 80 s + 80;
   tugofwar_time with c1 = 300, c2 = 500. *)

From Tugofwar.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Bool.
From KattisLib Require Import Cost.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ------------------------------------------------------------------ *)
(* Uint63 / PArray plumbing                                            *)
(* ------------------------------------------------------------------ *)

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma max_length_val : (φ PArray.max_length) = 4194303%Z.
Proof. reflexivity. Qed.

Lemma blength_set : forall (t : array bool) (i : int) (b : bool),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set bool t i b). Qed.

Lemma bget_set_same : forall (t : array bool) (i : int) (b : bool),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same bool t i b H). Qed.

Lemma bget_set_other : forall (t : array bool) (i j : int) (b : bool),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other bool t i j b H). Qed.

Lemma blength_make : forall (n : int) (b : bool),
  PArray.length (PArray.make n b)
  = if n <=? PArray.max_length then n else PArray.max_length.
Proof. intros n b. exact (length_make bool n b). Qed.

Lemma bget_make : forall (n i : int) (b : bool), (PArray.make n b).[i] = b.
Proof. intros n i b. exact (get_make bool b n i). Qed.

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
Elpi complexity orb.

Definition dist (m j : int) : Z := ((φ m) - (φ j))%Z.

Lemma dec_step : forall m i : int,
  (i <? m) = true -> Zwf 0 (dist m (i + 1)) (dist m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, dist. lia.
Qed.

Lemma dec_down : forall i : int,
  (0 <? i) = true -> Zwf 0 (φ (i - 1)) (φ i).
Proof.
  intros i H. rewrite ltb_spec in H. change (φ 0) with 0%Z in H.
  unfold Zwf. sia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* acc + a.[0] + ... + a.[i-1] *)
Fixpoint sum_loop (a : array uint) (i acc : int)
    (H : Acc (Zwf 0) (φ i)) {struct H} : int :=
  match bdec (0 <? i) with
  | left Hi => sum_loop a (i - 1) (acc + a.[i - 1]) (Acc_inv H (dec_down i Hi))
  | right _ => acc
  end.
Elpi complexity sum_loop.
Arguments sum_loop_cost : simpl never.

(* row c, cells s .. W-1: cell (c, s) |= cell (c-1, s-x) *)
Fixpoint cell_loop (t : array bool) (W x c s : int)
    (H : Acc (Zwf 0) (dist W s)) {struct H} : array bool :=
  match bdec (s <? W) with
  | left Hs =>
      cell_loop (if t.[(c - 1) * W + (s - x)] then t.[c * W + s <- true] else t)
        W x c (s + 1) (Acc_inv H (dec_step W s Hs))
  | right _ => t
  end.
Elpi complexity cell_loop.
Arguments cell_loop_cost : simpl never.

(* rows c, c-1, ..., 1, for a person of weight x *)
Fixpoint row_loop (t : array bool) (W x c : int)
    (H : Acc (Zwf 0) (φ c)) {struct H} : array bool :=
  match bdec (0 <? c) with
  | left Hc =>
      row_loop (cell_loop t W x c x (Zwf_well_founded 0 (dist W x)))
        W x (c - 1) (Acc_inv H (dec_down c Hc))
  | right _ => t
  end.
Elpi complexity row_loop.
Arguments row_loop_cost : simpl never.

(* people i-1, i-2, ..., 0 *)
Fixpoint item_loop (a : array uint) (t : array bool) (W K i : int)
    (H : Acc (Zwf 0) (φ i)) {struct H} : array bool :=
  match bdec (0 <? i) with
  | left Hi =>
      item_loop a (row_loop t W a.[i - 1] K (Zwf_well_founded 0 (φ K)))
        W K (i - 1) (Acc_inv H (dec_down i Hi))
  | right _ => t
  end.
Elpi complexity item_loop.
Arguments item_loop_cost : simpl never.

(* the largest s' <= s reachable with h or K people *)
Fixpoint best_loop (t : array bool) (W h K s : int)
    (H : Acc (Zwf 0) (φ s)) {struct H} : int :=
  if t.[h * W + s] || t.[K * W + s] then s
  else
    match bdec (0 <? s) with
    | left Hs => best_loop t W h K (s - 1) (Acc_inv H (dec_down s Hs))
    | right _ => 0
    end.
Elpi complexity best_loop.
Arguments best_loop_cost : simpl never.

Definition tugofwar_impl (a : array uint) : uint * uint :=
  let n := PArray.length a in
  let S := sum_loop a n 0 (Zwf_well_founded 0 (φ n)) in
  let half := S / 2 in
  let W := half + 1 in
  let h := n / 2 in
  let K := n - h in
  let t0 := (PArray.make ((K + 1) * W) false).[0 <- true] in
  let t := item_loop a t0 W K n (Zwf_well_founded 0 (φ n)) in
  let b := best_loop t W h K half (Zwf_well_founded 0 (φ half)) in
  (b, S - b).
Elpi complexity tugofwar_impl.
Arguments tugofwar_impl_cost : simpl never.

Lemma sum_loop_eq : forall a i acc H,
  sum_loop a i acc H =
  match bdec (0 <? i) with
  | left Hi => sum_loop a (i - 1) (acc + a.[i - 1]) (Acc_inv H (dec_down i Hi))
  | right _ => acc
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma cell_loop_eq : forall t W x c s H,
  cell_loop t W x c s H =
  match bdec (s <? W) with
  | left Hs =>
      cell_loop (if t.[(c - 1) * W + (s - x)] then t.[c * W + s <- true] else t)
        W x c (s + 1) (Acc_inv H (dec_step W s Hs))
  | right _ => t
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma row_loop_eq : forall t W x c H,
  row_loop t W x c H =
  match bdec (0 <? c) with
  | left Hc =>
      row_loop (cell_loop t W x c x (Zwf_well_founded 0 (dist W x)))
        W x (c - 1) (Acc_inv H (dec_down c Hc))
  | right _ => t
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma item_loop_eq : forall a t W K i H,
  item_loop a t W K i H =
  match bdec (0 <? i) with
  | left Hi =>
      item_loop a (row_loop t W a.[i - 1] K (Zwf_well_founded 0 (φ K)))
        W K (i - 1) (Acc_inv H (dec_down i Hi))
  | right _ => t
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma best_loop_eq : forall t W h K s H,
  best_loop t W h K s H =
  if t.[h * W + s] || t.[K * W + s] then s
  else
    match bdec (0 <? s) with
    | left Hs => best_loop t W h K (s - 1) (Acc_inv H (dec_down s Hs))
    | right _ => 0
    end.
Proof. intros. destruct H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Math side: reachability                                             *)
(* ------------------------------------------------------------------ *)

(* some choice b of people of l has c people and weight s *)
Definition reachZ (l : list N) (c s : Z) : Prop :=
  exists b : list bool, List.length b = List.length l /\
    Z.of_nat (List.length (team l b)) = c /\ Z.of_N (sum (team l b)) = s.

Lemma team_true : forall x l b, team (x :: l) (true :: b) = x :: team l b.
Proof. reflexivity. Qed.

Lemma team_false : forall x l b, team (x :: l) (false :: b) = team l b.
Proof. reflexivity. Qed.

Lemma reach_nonneg : forall l c s, reachZ l c s -> (0 <= c /\ 0 <= s)%Z.
Proof. intros l c s (b & _ & Hc & Hs). lia. Qed.

Lemma reach_nil : forall c s, reachZ [] c s <-> (c = 0 /\ s = 0)%Z.
Proof.
  intros c s. split.
  - intros (b & Hb & Hc & Hs). destruct b; [|discriminate]. simpl in *. lia.
  - intros [-> ->]. exists []. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma reach_cons : forall x l c s,
  reachZ (x :: l) c s <-> reachZ l c s \/ reachZ l (c - 1) (s - Z.of_N x).
Proof.
  intros x l c s. split.
  - intros (b & Hb & Hc & Hs). destruct b as [| b0 b]; [discriminate|].
    simpl in Hb. injection Hb as Hb.
    destruct b0.
    + right. exists b. rewrite team_true in Hc, Hs. simpl in Hc, Hs.
      split; [exact Hb|]. split; lia.
    + left. exists b. rewrite team_false in Hc, Hs. auto.
  - intros [(b & Hb & Hc & Hs) | (b & Hb & Hc & Hs)].
    + exists (false :: b). rewrite team_false. simpl. auto.
    + exists (true :: b). rewrite team_true. simpl. split; [lia|]. split; lia.
Qed.

Lemma len_team_other : forall l b, List.length b = List.length l ->
  (List.length (team l b) + List.length (other_team l b) = List.length l)%nat.
Proof.
  unfold other_team.
  induction l as [| x l IH]; intros b Hb; destruct b as [| b0 b]; try discriminate.
  - reflexivity.
  - simpl in Hb. injection Hb as Hb. destruct b0.
    + change (map negb (true :: b)) with (false :: map negb b).
      rewrite team_false, team_true. simpl. rewrite IH by exact Hb. reflexivity.
    + change (map negb (false :: b)) with (true :: map negb b).
      rewrite team_false, team_true. simpl. rewrite <- (IH b Hb). lia.
Qed.

Lemma sum_team_other : forall l b, List.length b = List.length l ->
  (sum (team l b) + sum (other_team l b) = sum l)%N.
Proof.
  unfold other_team.
  induction l as [| x l IH]; intros b Hb; destruct b as [| b0 b]; try discriminate.
  - reflexivity.
  - simpl in Hb. injection Hb as Hb. destruct b0.
    + change (map negb (true :: b)) with (false :: map negb b).
      rewrite team_false, team_true. simpl. rewrite <- (IH b Hb). lia.
    + change (map negb (false :: b)) with (true :: map negb b).
      rewrite team_false, team_true. simpl. rewrite <- (IH b Hb). lia.
Qed.

Lemma skipn_nth_cons : forall (l : list N) k, (k < List.length l)%nat ->
  skipn k l = nth k l 0%N :: skipn (S k) l.
Proof.
  induction l as [| x l IH]; intros k Hk; simpl in Hk; [lia|].
  destruct k as [| k]; [reflexivity|].
  simpl. apply IH. lia.
Qed.

Lemma sum_skipn_le : forall (l : list N) k, (sum (skipn k l) <= sum l)%N.
Proof.
  induction l as [| x l IH]; intros k; destruct k; simpl; try lia.
  specialize (IH k). lia.
Qed.

Lemma sum_bound : forall l : list N, Forall (fun x => 1 <= x <= 450)%N l ->
  (sum l <= 450 * N.of_nat (List.length l))%N.
Proof.
  induction l as [| x l IH]; intros H; simpl; [lia|].
  inversion H; subst. specialize (IH H3). lia.
Qed.

Lemma exists_count : forall (l : list N) c, (c <= List.length l)%nat ->
  exists b : list bool, List.length b = List.length l /\ List.length (team l b) = c.
Proof.
  induction l as [| x l IH]; intros c Hc.
  - exists []. simpl in *. split; [reflexivity | lia].
  - simpl in Hc. destruct c as [| c].
    + destruct (IH 0%nat ltac:(lia)) as (b & Hb & Hl).
      exists (false :: b). rewrite team_false. simpl. auto.
    + destruct (IH c ltac:(lia)) as (b & Hb & Hl).
      exists (true :: b). rewrite team_true. simpl. auto.
Qed.

(* ------------------------------------------------------------------ *)
(* Reading the input                                                   *)
(* ------------------------------------------------------------------ *)

Lemma repr_get : forall (a : array@{Set} uint) (w : list N), repr a w ->
  forall i : int, ((φ i) < Z.of_nat (List.length w))%Z ->
  (φ (PArray.get@{Set} a i)) = Z.of_N (nth (Z.to_nat (φ i)) w 0%N).
Proof.
  intros a w [Hl Hc] i Hi.
  destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (m & Hm & Hr).
  unfold repr, repr_uint in Hr.
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded i); lia).
  rewrite of_to_Z in Hr.
  assert (Hr' : Z.to_N (φ (PArray.get@{Set} a i)) = m) by exact Hr.
  rewrite (nth_error_nth w (Z.to_nat (φ i)) 0%N Hm).
  rewrite <- Hr'. pose proof (to_Z_bounded (PArray.get@{Set} a i)). lia.
Qed.

Lemma repr_length : forall (a : array@{Set} uint) (w : list N), repr a w ->
  (φ (PArray.length@{Set} a)) = Z.of_nat (List.length w).
Proof. intros a w [Hl _]. symmetry. exact Hl. Qed.

(* ------------------------------------------------------------------ *)
(* The table                                                           *)
(* ------------------------------------------------------------------ *)

Definition Bnd (W K : int) : Prop :=
  (1 <= (φ W) /\ ((φ K) + 1) * (φ W) <= 4194303)%Z.

Definition Tbl (t : array bool) (W K : int) (R : Z -> Z -> Prop) : Prop :=
  (φ (PArray.length t)) = (((φ K) + 1) * (φ W))%Z /\
  forall c s : int, ((φ c) <= (φ K))%Z -> ((φ s) < (φ W))%Z ->
    (t.[c * W + s] = true <-> R (φ c) (φ s)).

Lemma idx_spec : forall c s W K : int, Bnd W K ->
  ((φ c) <= (φ K))%Z -> ((φ s) < (φ W))%Z -> (φ (c * W + s)) = ((φ c) * (φ W) + (φ s))%Z.
Proof.
  intros c s W K [B1 B2] Hc Hs.
  pose proof (to_Z_bounded c). pose proof (to_Z_bounded s).
  pose proof (to_Z_bounded W). pose proof (to_Z_bounded K).
  assert (E : ((φ c) * (φ W) <= (φ K) * (φ W))%Z) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (E0 : (0 <= (φ c) * (φ W))%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (E1 : ((φ K) * (φ W) + (φ W) <= 4194303)%Z) by lia.
  rewrite add_spec, mul_spec.
  rewrite (Z.mod_small ((φ c) * (φ W))) by (rewrite wB_val; lia).
  apply Z.mod_small. rewrite wB_val. lia.
Qed.

Lemma idx_inj : forall c s c' s' W : Z,
  (0 <= s < W -> 0 <= s' < W -> 0 <= c -> 0 <= c' ->
   c * W + s = c' * W + s' -> c = c' /\ s = s')%Z.
Proof.
  intros c s c' s' W Hs Hs' Hc Hc' E.
  assert (c = c').
  { destruct (Z.lt_trichotomy c c') as [L | [L | L]]; [| exact L |].
    - assert ((c + 1) * W <= c' * W)%Z by (apply Z.mul_le_mono_nonneg_r; lia). lia.
    - assert ((c' + 1) * W <= c * W)%Z by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
  subst. lia.
Qed.

Lemma Tbl_ext : forall t W K R R', Tbl t W K R ->
  (forall c s, (0 <= c <= (φ K))%Z -> (0 <= s < (φ W))%Z -> (R c s <-> R' c s)) ->
  Tbl t W K R'.
Proof.
  intros t W K R R' [Hl Ht] HR. split; [exact Hl|].
  intros c s Hc Hs. rewrite Ht by assumption.
  pose proof (to_Z_bounded c). pose proof (to_Z_bounded s).
  apply HR; lia.
Qed.

Lemma Tbl_set : forall t W K R (i c0 s0 : int), Bnd W K -> Tbl t W K R ->
  ((φ c0) <= (φ K))%Z -> ((φ s0) < (φ W))%Z -> (φ i) = ((φ c0) * (φ W) + (φ s0))%Z ->
  Tbl t.[i <- true] W K (fun c s => (c = (φ c0) /\ s = (φ s0)) \/ R c s).
Proof.
  intros t W K R i c0 s0 B [Hl Ht] Hc0 Hs0 Hi.
  split; [rewrite blength_set; exact Hl|].
  intros c s Hc Hs.
  pose proof (idx_spec c s W K B Hc Hs) as Ei.
  pose proof (to_Z_bounded c). pose proof (to_Z_bounded s).
  pose proof (to_Z_bounded c0). pose proof (to_Z_bounded s0).
  destruct (Uint63.eqb_spec i (c * W + s)) as [E _].
  destruct (i =? c * W + s) eqn:Eq.
  - specialize (E eq_refl). rewrite <- E.
    rewrite bget_set_same.
    + split; [intros _; left|tauto].
      rewrite E, Ei in Hi. apply idx_inj with (W := (φ W)); lia.
    + rewrite ltb_spec, Hl, Hi. destruct B.
      assert ((φ c0) * (φ W) <= (φ K) * (φ W))%Z by (apply Z.mul_le_mono_nonneg_r; lia).
      lia.
  - rewrite bget_set_other.
    + rewrite Ht by assumption. split; [tauto|].
      intros [[C S] | HR]; [|exact HR].
      exfalso. rewrite <- Bool.not_true_iff_false in Eq. apply Eq.
      apply Uint63.eqb_spec. apply to_Z_inj. rewrite Ei, Hi. rewrite C, S. reflexivity.
    + intro F. assert (X : (i =? c * W + s) = true) by (apply Uint63.eqb_spec; exact F).
      congruence.
Qed.

(* ------------------------------------------------------------------ *)
(* The loops                                                           *)
(* ------------------------------------------------------------------ *)

Definition Hpos (P : Z -> Z -> Prop) : Prop :=
  forall c s, P c s -> (0 <= c /\ 0 <= s)%Z.

Definition step (P : Z -> Z -> Prop) (xz : Z) (c s : Z) : Prop :=
  P c s \/ P (c - 1)%Z (s - xz)%Z.

Lemma cell_loop_spec : forall (P : Z -> Z -> Prop) (t : array bool) (W K x c0 : int),
  Bnd W K -> Hpos P -> (1 <= (φ c0) <= (φ K))%Z ->
  forall (z : Z) (s : int) (H : Acc (Zwf 0) (dist W s)),
  dist W s = z -> ((φ x) <= (φ s))%Z ->
  Tbl t W K (fun c s' =>
    if ((φ c0) <? c)%Z then step P (φ x) c s'
    else if (c =? (φ c0))%Z then
      (if (s' <? (φ s))%Z then step P (φ x) c s' else P c s')
    else P c s') ->
  Tbl (cell_loop t W x c0 s H) W K (fun c s' =>
    if ((φ c0) <=? c)%Z then step P (φ x) c s' else P c s').
Proof.
  intros P t0 W K x c0 B Hp Hc0 z. revert t0.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros t s H Hz Hxs Ht.
  rewrite cell_loop_eq.
  pose proof (to_Z_bounded s). pose proof (to_Z_bounded x).
  pose proof (to_Z_bounded c0). pose proof (to_Z_bounded W).
  destruct (bdec (s <? W)) as [Hs | Hs].
  - pose proof Hs as Hs'. rewrite ltb_spec in Hs'.
    assert (Hs1 : (φ (s + 1)) = ((φ s) + 1)%Z) by sia.
    assert (Ec : (φ (c0 - 1)) = ((φ c0) - 1)%Z) by sia.
    assert (Es : (φ (s - x)) = ((φ s) - (φ x))%Z) by sia.
    assert (Hread : t.[(c0 - 1) * W + (s - x)] = true <->
                    P ((φ c0) - 1)%Z ((φ s) - (φ x))%Z).
    { destruct Ht as [_ Ht]. rewrite Ht by lia. rewrite Ec, Es.
      destruct (Z.ltb_spec (φ c0) ((φ c0) - 1)); [lia|].
      destruct (Z.eqb_spec ((φ c0) - 1) (φ c0)); [lia|]. tauto. }
    eapply IH; [ | reflexivity | lia | ].
    + rewrite <- Hz. apply dec_step. exact Hs.
    + destruct (t.[(c0 - 1) * W + (s - x)]) eqn:Er.
      * apply Tbl_ext with (R := fun c s' => (c = (φ c0) /\ s' = (φ s)) \/
          (if ((φ c0) <? c)%Z then step P (φ x) c s'
           else if (c =? (φ c0))%Z then
             (if (s' <? (φ s))%Z then step P (φ x) c s' else P c s')
           else P c s')).
        -- apply Tbl_set with (c0 := c0) (s0 := s); [exact B | exact Ht | lia | lia |].
           apply idx_spec with (K := K); [exact B | lia | lia].
        -- intros c s' Hc Hs''. cbv beta. rewrite Hs1.
           assert (Pr : P ((φ c0) - 1)%Z ((φ s) - (φ x))%Z) by (apply Hread; reflexivity).
           destruct (Z.ltb_spec (φ c0) c); [split; [intros [[C _] | X]; [lia | exact X] | tauto]|].
           destruct (Z.eqb_spec c (φ c0)); [subst c|].
           ++ destruct (Z.ltb_spec s' (φ s)); destruct (Z.ltb_spec s' ((φ s) + 1));
                try lia.
              ** split; [intros [[_ S] | X]; [lia | exact X] | tauto].
              ** assert (s' = (φ s)) by lia. subst s'.
                 split; [intros _ | intros _; left; auto].
                 right. exact Pr.
              ** split; [intros [[_ S] | X]; [lia | exact X] | tauto].
           ++ split; [intros [[C _] | X]; [lia | exact X] | tauto].
      * apply Tbl_ext with (1 := Ht).
        intros c s' Hc Hs''. cbv beta. rewrite Hs1.
        assert (Pr : ~ P ((φ c0) - 1)%Z ((φ s) - (φ x))%Z)
          by (intro F; apply Hread in F; discriminate).
        destruct (Z.ltb_spec (φ c0) c); [tauto|].
        destruct (Z.eqb_spec c (φ c0)); [subst c|tauto].
        destruct (Z.ltb_spec s' (φ s)); destruct (Z.ltb_spec s' ((φ s) + 1));
          try lia; try tauto.
        assert (s' = (φ s)) by lia. subst s'. unfold step. tauto.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hs.
    apply Tbl_ext with (1 := Ht).
    intros c s' Hc Hs''. cbv beta.
    destruct (Z.ltb_spec (φ c0) c); destruct (Z.leb_spec (φ c0) c); try lia; try tauto;
    destruct (Z.eqb_spec c (φ c0)); try lia; try tauto;
    destruct (Z.ltb_spec s' (φ s)); try lia; tauto.
Qed.

Lemma row_loop_spec : forall (P : Z -> Z -> Prop) (t : array bool) (W K x : int),
  Bnd W K -> Hpos P ->
  forall (z : Z) (c : int) (H : Acc (Zwf 0) (φ c)),
  (φ c) = z -> ((φ c) <= (φ K))%Z ->
  Tbl t W K (fun c' s' => if ((φ c) <? c')%Z then step P (φ x) c' s' else P c' s') ->
  Tbl (row_loop t W x c H) W K (step P (φ x)).
Proof.
  intros P t0 W K x B Hp z. revert t0.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros t c H Hz HcK Ht.
  rewrite row_loop_eq.
  pose proof (to_Z_bounded c). pose proof (to_Z_bounded x).
  destruct (bdec (0 <? c)) as [Hc | Hc].
  - pose proof Hc as Hc'. rewrite ltb_spec in Hc'. change (φ 0) with 0%Z in Hc'.
    assert (Ec : (φ (c - 1)) = ((φ c) - 1)%Z) by sia.
    eapply IH; [ | reflexivity | lia | ].
    + rewrite <- Hz. apply dec_down. exact Hc.
    + rewrite Ec.
      eapply Tbl_ext.
      * apply (cell_loop_spec P t W K x c B Hp ltac:(lia) _ x _ eq_refl ltac:(lia)).
        apply Tbl_ext with (1 := Ht).
        intros c' s' Hc'' Hs''. cbv beta.
        destruct (Z.ltb_spec (φ c) c'); [tauto|].
        destruct (Z.eqb_spec c' (φ c)); [subst c'|tauto].
        destruct (Z.ltb_spec s' (φ x)); [|tauto].
        unfold step. split; [tauto | intros [X | X]; [exact X|]].
        apply Hp in X. lia.
      * intros c' s' Hc'' Hs''. cbv beta.
        destruct (Z.leb_spec (φ c) c'); destruct (Z.ltb_spec ((φ c) - 1) c');
          try lia; tauto.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hc. change (φ 0) with 0%Z in Hc.
    apply Tbl_ext with (1 := Ht).
    intros c' s' Hc'' Hs''. cbv beta.
    destruct (Z.ltb_spec (φ c) c'); [tauto|].
    unfold step. split; [tauto|]. intros [X | X]; [exact X|].
    apply Hp in X. lia.
Qed.

Lemma item_loop_spec : forall (w : list N) (a : array uint), repr a w ->
  forall (t : array bool) (W K : int), Bnd W K ->
  forall (z : Z) (i : int) (H : Acc (Zwf 0) (φ i)),
  (φ i) = z -> ((φ i) <= Z.of_nat (List.length w))%Z ->
  Tbl t W K (reachZ (skipn (Z.to_nat (φ i)) w)) ->
  Tbl (item_loop a t W K i H) W K (reachZ w).
Proof.
  intros w a Ha t0 W K B z.
  revert t0.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros t i H Hz Hi Ht.
  rewrite item_loop_eq.
  pose proof (to_Z_bounded i).
  destruct (bdec (0 <? i)) as [Hc | Hc].
  - pose proof Hc as Hc'. rewrite ltb_spec in Hc'. change (φ 0) with 0%Z in Hc'.
    assert (Ei : (φ (i - 1)) = ((φ i) - 1)%Z) by sia.
    eapply IH; [ | reflexivity | lia | ].
    + rewrite <- Hz. apply dec_down. exact Hc.
    + eapply Tbl_ext.
      * apply (row_loop_spec (reachZ (skipn (Z.to_nat (φ i)) w)) t W K
                 a.[i - 1] B (reach_nonneg _) _ K _ eq_refl ltac:(lia)).
        apply Tbl_ext with (1 := Ht).
        intros c' s' Hc'' Hs''. cbv beta.
        destruct (Z.ltb_spec (φ K) c'); [lia | tauto].
      * intros c' s' Hc'' Hs''. cbv beta.
        rewrite Ei.
        rewrite (skipn_nth_cons w (Z.to_nat ((φ i) - 1))) by lia.
        replace (S (Z.to_nat ((φ i) - 1))) with (Z.to_nat (φ i)) by lia.
        rewrite reach_cons. unfold step.
        rewrite (repr_get a w Ha (i - 1)) by lia. rewrite Ei. tauto.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hc. change (φ 0) with 0%Z in Hc.
    replace (Z.to_nat (φ i)) with 0%nat in Ht by lia. exact Ht.
Qed.

Lemma sum_loop_spec : forall (w : list N) (a : array uint), repr a w ->
  (Z.of_N (sum w) <= 45000)%Z ->
  forall (z : Z) (i acc : int) (H : Acc (Zwf 0) (φ i)),
  (φ i) = z -> ((φ i) <= Z.of_nat (List.length w))%Z ->
  (φ acc) = Z.of_N (sum (skipn (Z.to_nat (φ i)) w)) ->
  (φ (sum_loop a i acc H)) = Z.of_N (sum w).
Proof.
  intros w a Ha HS z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i acc H Hz Hi Hacc.
  rewrite sum_loop_eq.
  pose proof (to_Z_bounded i).
  destruct (bdec (0 <? i)) as [Hc | Hc].
  - pose proof Hc as Hc'. rewrite ltb_spec in Hc'. change (φ 0) with 0%Z in Hc'.
    assert (Ei : (φ (i - 1)) = ((φ i) - 1)%Z) by sia.
    eapply IH; [ | reflexivity | lia | ].
    + rewrite <- Hz. apply dec_down. exact Hc.
    + rewrite Ei.
      pose proof (sum_skipn_le w (Z.to_nat ((φ i) - 1))) as Hle.
      rewrite (skipn_nth_cons w (Z.to_nat ((φ i) - 1))) in Hle |- * by lia.
      replace (S (Z.to_nat ((φ i) - 1))) with (Z.to_nat (φ i)) in Hle |- * by lia.
      pose proof (repr_get a w Ha (i - 1) ltac:(lia)) as G. rewrite Ei in G.
      simpl in Hle |- *.
      rewrite add_spec, Hacc, G, N2Z.inj_add, Z.add_comm. apply Z.mod_small. rewrite wB_val. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hc. change (φ 0) with 0%Z in Hc.
    replace (Z.to_nat (φ i)) with 0%nat in Hacc by lia. exact Hacc.
Qed.

Lemma best_loop_spec : forall (t : array bool) (W h K : int) (R : Z -> Z -> Prop),
  Bnd W K -> ((φ h) <= (φ K))%Z -> Tbl t W K R ->
  forall (z : Z) (s : int) (H : Acc (Zwf 0) (φ s)),
  (φ s) = z -> ((φ s) < (φ W))%Z ->
  (exists s0, (0 <= s0 <= (φ s))%Z /\ (R (φ h) s0 \/ R (φ K) s0)) ->
  ((φ (best_loop t W h K s H)) <= (φ s))%Z /\
  (R (φ h) (φ (best_loop t W h K s H)) \/ R (φ K) (φ (best_loop t W h K s H))) /\
  forall s', ((φ (best_loop t W h K s H)) < s' <= (φ s))%Z -> ~ (R (φ h) s' \/ R (φ K) s').
Proof.
  intros t W h K R B Hh [Hl Ht] z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros s H Hz Hs Hex.
  rewrite best_loop_eq.
  pose proof (to_Z_bounded s).
  destruct (t.[h * W + s] || t.[K * W + s]) eqn:Eb.
  - split; [lia|]. split; [|intros; lia].
    apply orb_true_iff in Eb. destruct Eb as [E | E].
    + left. apply Ht; [lia | lia | exact E].
    + right. apply Ht; [lia | lia | exact E].
  - apply orb_false_iff in Eb. destruct Eb as [E1 E2].
    assert (Hn : ~ (R (φ h) (φ s) \/ R (φ K) (φ s))).
    { intros [X | X].
      - apply (Ht h s) in X; [| lia | lia]. congruence.
      - apply (Ht K s) in X; [| lia | lia]. congruence. }
    destruct (bdec (0 <? s)) as [Hc | Hc].
    + pose proof Hc as Hc'. rewrite ltb_spec in Hc'. change (φ 0) with 0%Z in Hc'.
      assert (Es : (φ (s - 1)) = ((φ s) - 1)%Z) by sia.
      destruct (IH (φ (s - 1))) with (s := s - 1)
        (H := Acc_inv H (dec_down s Hc)) as (I1 & I2 & I3);
        [ rewrite <- Hz; apply dec_down; exact Hc | reflexivity | lia | | ].
      * destruct Hex as (s0 & Hs0 & Hr). exists s0. split; [|exact Hr].
        destruct (Z.eq_dec s0 (φ s)); [subst; contradiction|]. lia.
      * split; [lia|]. split; [exact I2|].
        intros s' Hs'. destruct (Z.eq_dec s' (φ s)); [subst; exact Hn|].
        apply I3. lia.
    + exfalso. rewrite <- Bool.not_true_iff_false, ltb_spec in Hc.
      change (φ 0) with 0%Z in Hc.
      destruct Hex as (s0 & Hs0 & Hr).
      assert (s0 = (φ s)) by lia. subst. contradiction.
Qed.

(* ------------------------------------------------------------------ *)
(* From the best reachable sum to the spec                             *)
(* ------------------------------------------------------------------ *)

Section Final.
  Variable w : list N.
  Let n : Z := Z.of_nat (List.length w).
  Let S : Z := Z.of_N (sum w).
  Let h : Z := (n / 2)%Z.
  Let K : Z := (n - n / 2)%Z.
  Let half : Z := (S / 2)%Z.

  Definition good (v : Z) : Prop := reachZ w h v \/ reachZ w K v.

  (* a balanced division gives a good sum at most half: its first team or
     its other team *)
  Lemma division_good : forall bl, division w bl ->
    let t := Z.of_N (sum (team w bl)) in
    (t <= half /\ good t \/ S - t <= half /\ good (S - t))%Z.
  Proof.
    intros bl [Hl Hd] t.
    unfold len in Hl. assert (Hl' : List.length bl = List.length w) by lia.
    pose proof (len_team_other w bl Hl') as Lc.
    pose proof (sum_team_other w bl Hl') as Sc.
    unfold len in Hd.
    set (c := List.length (team w bl)) in *.
    set (c' := List.length (other_team w bl)) in *.
    assert (Hc : (Z.of_nat c = h \/ Z.of_nat c = K)%Z).
    { unfold h, K, n. rewrite <- Lc. rewrite !nat_N_Z in Hd. sia. }
    assert (Hc' : (Z.of_nat c' = h \/ Z.of_nat c' = K)%Z).
    { unfold h, K, n. rewrite <- Lc. rewrite !nat_N_Z in Hd. sia. }
    assert (Ht : (0 <= t)%Z) by lia.
    destruct (Z.le_gt_cases t half).
    - left. split; [assumption|].
      assert (R : reachZ w (Z.of_nat c) t) by (exists bl; auto).
      unfold good. destruct Hc as [E | E]; rewrite <- E; auto.
    - right. split.
      + unfold half, t, S in *. rewrite <- Sc. lia.
      + assert (R : reachZ w (Z.of_nat c') (S - t)).
        { exists (map negb bl). split; [rewrite length_map; exact Hl'|].
          split; [reflexivity|]. unfold t, S. rewrite <- Sc. fold (other_team w bl). lia. }
        unfold good. destruct Hc' as [E | E]; rewrite <- E; auto.
  Qed.

  Lemma final_spec : forall b : Z,
    (0 <= b <= half)%Z -> good b ->
    (forall v, b < v <= half -> ~ good v)%Z ->
    tugofwar_spec w (Z.to_N b, Z.to_N (S - b)).
  Proof.
    intros b Hb Hg Hmax.
    assert (Hge : forall v, (0 <= v <= half)%Z -> good v -> (v <= b)%Z).
    { intros v Hv Gv. destruct (Z.le_gt_cases v b); [assumption|].
      exfalso. apply (Hmax v); [lia | exact Gv]. }
    assert (HS : (0 <= S)%Z) by (unfold S; lia).
    unfold tugofwar_spec. split; [unfold half in Hb; lia|].
    assert (Hn : (0 <= n)%Z) by (unfold n; lia).
    destruct Hg as [Hr | Hr]; destruct Hr as (bl & Hl & Hc & Hs);
      exists bl;
      pose proof (len_team_other w bl Hl) as Lc;
      pose proof (sum_team_other w bl Hl) as Sc.
    all: split; [split; [unfold len; rewrite Hl; reflexivity|]
                 ; unfold len; rewrite !nat_N_Z;
                   unfold h, K, n in Hc; sia|].
    all: split; [lia|].
    all: split; [unfold S in *; lia|].
    all: intros s' Hd'.
    all: pose proof (division_good s' Hd') as Dg; simpl in Dg.
    all: assert (Ss : (Z.of_N (sum (team w s')) + Z.of_N (sum (other_team w s')) = S)%Z)
           by (destruct Hd' as [Hl' _]; unfold len in Hl';
               unfold S; rewrite <- (sum_team_other w s') by lia; lia).
    all: unfold gap; unfold S in *.
    all: destruct Dg as [[D1 D2] | [D1 D2]];
         [pose proof (Hge (Z.of_N (sum (team w s'))) ltac:(lia) D2)
         | pose proof (Hge (Z.of_N (sum w) - Z.of_N (sum (team w s')))%Z ltac:(lia) D2)];
         unfold half, S in *; sia.
  Qed.
End Final.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Lemma tugofwar_impl_correct : forall (w : list N) (x : array uint),
  valid_input w -> repr x w ->
  exists o : N * N, repr (tugofwar_impl x) o /\ tugofwar_spec w o.
Proof.
  intros w a [Hn Hw] Ha.
  unfold len in Hn.
  pose proof (repr_length a w Ha) as La.
  pose proof (sum_bound w Hw) as Sb.
  assert (HS : (Z.of_N (sum w) <= 45000)%Z) by lia.
  set (n := PArray.length a) in *.
  set (Sint := sum_loop a n 0 (Zwf_well_founded 0 (φ n))).
  assert (ES : (φ Sint) = Z.of_N (sum w)).
  { apply (sum_loop_spec w a Ha HS _ n 0 _ eq_refl ltac:(lia)).
    replace (Z.to_nat (φ n)) with (List.length w) by lia.
    rewrite skipn_all. reflexivity. }
  set (half := Sint / 2).
  set (W := half + 1).
  set (h := n / 2).
  set (K := n - h).
  assert (Ehalf : (φ half) = ((φ Sint) / 2)%Z) by (unfold half; sia).
  assert (EW : (φ W) = ((φ Sint) / 2 + 1)%Z) by (unfold W; sia).
  assert (Eh : (φ h) = ((φ n) / 2)%Z) by (unfold h; sia).
  assert (EK : (φ K) = ((φ n) - (φ n) / 2)%Z) by (unfold K; sia).
  assert (B : Bnd W K).
  { split; [lia|]. rewrite EW, EK.
    assert ((φ n) - (φ n) / 2 + 1 <= 51)%Z by sia.
    assert ((φ Sint) / 2 + 1 <= 22501)%Z by sia.
    assert (0 <= (φ Sint) / 2)%Z by sia.
    nia. }
  set (L := (K + 1) * W).
  assert (EL : (φ L) = (((φ K) + 1) * (φ W))%Z).
  { unfold L. destruct B as [B1 B2].
    assert (EK1 : (φ (K + 1)) = ((φ K) + 1)%Z) by (rewrite EK; sia).
    rewrite mul_spec, EK1. apply Z.mod_small.
    pose proof (to_Z_bounded K).
    assert (0 <= ((φ K) + 1) * (φ W))%Z by (apply Z.mul_nonneg_nonneg; lia).
    rewrite wB_val. lia. }
  assert (Hmk : PArray.length (PArray.make L false) = L).
  { rewrite blength_make.
    replace (L <=? PArray.max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val, EL. destruct B. lia. }
  set (t0 := (PArray.make L false).[0 <- true]).
  assert (T0 : Tbl t0 W K (reachZ (skipn (Z.to_nat (φ n)) w))).
  { replace (Z.to_nat (φ n)) with (List.length w) by lia. rewrite skipn_all.
    apply Tbl_ext with (R := fun c s => (c = (φ 0) /\ s = (φ 0)) \/ False).
    - apply Tbl_set with (c0 := 0) (s0 := 0); [exact B | | lia | lia | reflexivity].
      split; [rewrite Hmk; exact EL|].
      intros c s _ _. rewrite bget_make. split; [discriminate | tauto].
    - intros c s _ _. rewrite reach_nil. change (φ 0) with 0%Z. tauto. }
  set (t := item_loop a t0 W K n (Zwf_well_founded 0 (φ n))).
  assert (T : Tbl t W K (reachZ w))
    by (apply (item_loop_spec w a Ha t0 W K B _ n _ eq_refl ltac:(lia) T0)).
  (* some division exists: the first n/2 people against the others *)
  assert (Hex : exists s0, (0 <= s0 <= (φ half))%Z /\
                  (reachZ w (φ h) s0 \/ reachZ w (φ K) s0)).
  { destruct (exists_count w (List.length w / 2)) as (bl & Hbl & Hc);
      [apply Nat.div_le_upper_bound; lia|].
    assert (Hd : division w bl).
    { pose proof (len_team_other w bl Hbl) as Lc.
      split; [unfold len; rewrite Hbl; reflexivity|].
      unfold len. rewrite !nat_N_Z. rewrite Hc in Lc |- *.
      pose proof (Nat.div_mod (List.length w) 2 ltac:(lia)).
      pose proof (Nat.mod_upper_bound (List.length w) 2 ltac:(lia)). lia. }
    pose proof (division_good w bl Hd) as D. simpl in D.
    rewrite Eh, EK, Ehalf, ES, La.
    pose proof (sum_team_other w bl Hbl).
    destruct D as [[D1 D2] | [D1 D2]]; eexists; (split; [|exact D2]);
      lia. }
  destruct (best_loop_spec t W h K (reachZ w) B ltac:(lia) T _ half (Zwf_well_founded 0 (φ half)) eq_refl
              ltac:(lia) Hex) as (R1 & R2 & R3).
  set (b := best_loop t W h K half (Zwf_well_founded 0 (φ half))) in *.
  exists (Z.to_N (φ b), Z.to_N ((φ Sint) - (φ b))).
  pose proof (to_Z_bounded b).
  split.
  - change (tugofwar_impl a) with (b, Sint - b).
    split; [reflexivity|].
    unfold repr, repr_uint. cbn [snd]. f_equal. sia.
  - rewrite ES.
    apply final_spec.
    + lia.
    + unfold good. rewrite Eh, EK, La in R2. exact R2.
    + intros v Hv. rewrite Eh, EK, La in R3. apply R3. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition tugofwar : array uint -> uint * uint := tugofwar_impl.
Elpi complexity tugofwar.

Definition tugofwar_correct : forall (w : list N) (x : array uint),
  valid_input w -> repr x w ->
  exists o : N * N, repr (tugofwar x) o /\ tugofwar_spec w o
  := tugofwar_impl_correct.

(* ------------------------------------------------------------------ *)
(* Cost                                                                *)
(* ------------------------------------------------------------------ *)

(* The total weight is [sizes] of the input. *)
Lemma sizes_eq (a : array uint) (w : list N) : repr a w -> sizes a = N.to_nat (sum w).
Proof.
  intros Ha. pose proof (repr_length a w Ha) as La.
  unfold sizes.
  assert (Hs : size a = List.length w).
  { unfold size, size_array. match goal with |- Z.to_nat (φ ?l) = _ => change l with (PArray.length@{Set} a) end. lia. }
  rewrite Hs.
  assert (G : forall k acc, (k <= List.length w)%nat ->
    List.fold_left (fun (acc i : nat) => (acc + size a.[of_Z (Z.of_nat i)])%nat)
      (List.seq k (List.length w - k)) acc = (acc + N.to_nat (sum (skipn k w)))%nat).
  { intros k. remember (List.length w - k)%nat as d eqn:Ed. revert k Ed.
    induction d as [|d IH]; intros k Ed acc Hk.
    - replace k with (List.length w) by lia. rewrite skipn_all. cbn. lia.
    - cbn [List.seq List.fold_left].
      rewrite (IH (S k) ltac:(lia)) by lia.
      rewrite (skipn_nth_cons w k) by lia. cbn [sum fold_right].
      fold (sum (skipn (S k) w)).
      assert (Hg : size a.[of_Z (Z.of_nat k)] = N.to_nat (nth k w 0%N)).
      { unfold size, size_uint.
        pose proof (repr_get a w Ha (of_Z (Z.of_nat k))) as G.
        assert (Ek : φ (of_Z (Z.of_nat k)) = Z.of_nat k).
        { rewrite of_Z_spec. apply Z.mod_small. rewrite wB_val.
          pose proof (PArray.leb_length _ a) as HH. rewrite leb_spec in HH.
          change (φ max_length) with 4194303%Z in HH.
          assert (Z.of_nat (List.length w) <= 4194303)%Z.
          { rewrite <- La. exact HH. } lia. }
        rewrite Ek in G. specialize (G ltac:(lia)). rewrite Nat2Z.id in G.
        match goal with |- Z.to_nat (φ ?g) = _ => change g with (PArray.get@{Set} a (of_Z (Z.of_nat k))) end.
        rewrite G. lia. }
      rewrite Hg. lia. }
  specialize (G 0%nat 0%nat (Nat.le_0_l _)). rewrite Nat.sub_0_r in G. transitivity (0 + N.to_nat (sum (skipn 0 w)))%nat; [exact G | reflexivity].
Qed.

From Stdlib Require Import ssreflect.

(* [cbn] (inside [cost_simpl]) must not unfold [φ] of a variable (the [Acc]
   indices of the loops) nor the measure [dist]. *)
#[local] Arguments Uint63.to_Z : simpl never.
#[local] Arguments dist : simpl never.

Lemma bdec_time b (w : bool_cost stepsCM b) : (cost (bdec_cost stepsCM b w) <= 2)%nat.
Proof. destruct w; cbn; lia. Qed.

Lemma down_lt i : (0 <? i) = true -> (Z.to_nat (φ (i - 1)) < Z.to_nat (φ i))%nat.
Proof. intros H. pose proof (dec_down i H) as [_ X]. lia. Qed.

Lemma sum_loop_time a aC i iC acc accC H HC :
  (cost (extract (extract (extract (sum_loop_cost stepsCM a aC) i iC) acc accC) H HC) <= 50 * Z.to_nat (φ i) + 10)%nat.
Proof.
  unfold sum_loop_cost. cbn.
  match goal with |- context [@cost ?T (?G a aC i iC acc accC H HC)] =>
    assert (HG : forall m i iC acc accC H HC, (Z.to_nat (φ i) <= m)%nat ->
       (cost (G a aC i iC acc accC H HC) <= 50 * m + 10)%nat) end.
  { induction m as [|m IH]; intros i' iC' acc' accC' [g] HC' Hm;
      cost_simpl;
      pose proof (bdec_time (0 <? i') (bool_w (0 <? i'))) as HB;
      cost_destruct (bdec (0 <? i')); cost_simpl.
    - exfalso. pose proof (down_lt i' e). lia.
    - lia.
    - pose proof (down_lt i' e) as Hg.
      assert (Hm' : (Z.to_nat (φ (i' - 1)) <= m)%nat) by lia.
      match goal with |- context [@cost ?T (?G' a aC (i' - 1)%uint63 ?w ?ac ?acC ?h ?e)] =>
        have HI := (IH (i' - 1)%uint63 w ac acC h e Hm' : (@cost T (G' a aC (i' - 1)%uint63 w ac acC h e) <= _)%nat) end.
      lia.
    - lia. }
  match goal with |- context [@cost ?T (?G a aC i iC acc accC H HC)] =>
    exact (HG _ i iC acc accC H HC (le_n _) : (@cost T (G a aC i iC acc accC H HC) <= _)%nat) end.
Qed.

Lemma step_lt m i : (i <? m) = true -> (Z.to_nat (dist m (i + 1)) < Z.to_nat (dist m i))%nat.
Proof. intros H. pose proof (dec_step m i H) as [_ X]. unfold dist in *. lia. Qed.

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

Lemma cell_loop_time t0 tc w0 wc x0 xc c0 ccc s0 sc H hc :
  (cost (extract (extract (extract (extract (extract (cell_loop_cost stepsCM t0 tc) w0 wc) x0 xc) c0 ccc) s0 sc) H hc) <= 50 * Z.to_nat (dist w0 s0) + 10)%nat.
Proof.
  unfold cell_loop_cost. cbn.
  match goal with |- context [@cost ?T (?G t0 tc w0 wc x0 xc c0 ccc s0 sc H hc)] =>
    assert (HG : forall m t0 tc s0 sc H hc, (Z.to_nat (dist w0 s0) <= m)%nat ->
       (cost (G t0 tc w0 wc x0 xc c0 ccc s0 sc H hc) <= 50 * m + 10)%nat) end.
  { induction m as [|m IH]; intros t' tc' s' sc' [g] hc' Hm;
      cost_simpl;
      pose proof (bdec_time (s' <? w0) (bool_w (s' <? w0))) as HB;
      cost_destruct (bdec (s' <? w0)); cost_simpl.
    - exfalso. pose proof (step_lt w0 s' e). lia.
    - lia.
    - pose proof (step_lt w0 s' e) as Hg.
      assert (Hm' : (Z.to_nat (dist w0 (s' + 1)) <= m)%nat) by lia.
      generalize (array_elems tc' ((c0 - 1) * w0 + (s' - x0))).
      cost_destruct (t'.[(c0 - 1) * w0 + (s' - x0)]); intros wt;
      cost_simpl; set_simpl;
      match goal with |- context [@cost ?T (?G' ?tt ?ttc w0 wc x0 xc c0 ccc (s' + 1)%uint63 ?w ?h ?e)] =>
        have HI := (IH tt ttc (s' + 1)%uint63 w h e Hm' : (@cost T (G' tt ttc w0 wc x0 xc c0 ccc (s' + 1)%uint63 w h e) <= _)%nat) end;
      lia.
    - lia. }
  match goal with |- context [@cost ?T (?G t0 tc w0 wc x0 xc c0 ccc s0 sc H hc)] =>
    exact (HG _ t0 tc s0 sc H hc (le_n _) : (@cost T (G t0 tc w0 wc x0 xc c0 ccc s0 sc H hc) <= _)%nat) end.
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

Ltac gen_cell := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (extract (cell_loop_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC =>
    let Hc := fresh "Hcell" in
    have Hc := (cell_loop_time a aC b bC c cC d dC e eC f fC : (@cost T X <= _)%nat);
    revert Hc; generalize (@cost T X); intros ? Hc end end.

Lemma dist_le w x : (Z.to_nat (dist w x) <= Z.to_nat (φ w))%nat.
Proof. unfold dist. pose proof (to_Z_bounded x). lia. Qed.

Lemma row_loop_time t0 tc w0 wc x0 xc c0 ccc H hc :
  (cost (extract (extract (extract (extract (row_loop_cost stepsCM t0 tc) w0 wc) x0 xc) c0 ccc) H hc) <= (50 * Z.to_nat (φ w0) + 50) * Z.to_nat (φ c0) + 10)%nat.
Proof.
  remember (Z.to_nat (φ w0)) as GW eqn:EGW.
  unfold row_loop_cost. cbn.
  match goal with |- context [@cost ?T (?G t0 tc w0 wc x0 xc c0 ccc H hc)] =>
    assert (HG : forall m t0 tc c0 ccc H hc, (Z.to_nat (φ c0) <= m)%nat ->
       (cost (G t0 tc w0 wc x0 xc c0 ccc H hc) <= (50 * GW + 50) * m + 10)%nat) end.
  { induction m as [|m IH]; intros t' tc' c' cc' [g] hc' Hm;
      cost_simpl;
      pose proof (bdec_time (0 <? c') (bool_w (0 <? c'))) as HB;
      cost_destruct (bdec (0 <? c')); cost_simpl.
    - exfalso. pose proof (down_lt c' e). lia.
    - lia.
    - pose proof (down_lt c' e) as Hg.
      assert (Hm' : (Z.to_nat (φ (c' - 1)) <= m)%nat) by lia.
      z0 cell_loop_cost; z1 cell_loop_cost; z2 cell_loop_cost; z3 cell_loop_cost; z4 cell_loop_cost.
      gen_cell. pose proof (dist_le w0 x0). rewrite <- EGW in *.
      z0 row_loop_cost; z1 row_loop_cost; z2 row_loop_cost; z3 row_loop_cost.
      match goal with |- context [@cost ?T (?G' ?tt ?ttc w0 wc x0 xc (c' - 1)%uint63 ?w ?h ?e)] =>
        have HI := (IH tt ttc (c' - 1)%uint63 w h e Hm' : (@cost T (G' tt ttc w0 wc x0 xc (c' - 1)%uint63 w h e) <= _)%nat) end.
      nia.
    - lia. }
  match goal with |- context [@cost ?T (?G t0 tc w0 wc x0 xc c0 ccc H hc)] =>
    exact (HG _ t0 tc c0 ccc H hc (le_n _) : (@cost T (G t0 tc w0 wc x0 xc c0 ccc H hc) <= _)%nat) end.
Qed.

Ltac gen_row := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (row_loop_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC =>
    let Hc := fresh "Hrow" in
    have Hc := (row_loop_time a aC b bC c cC d dC e eC : (@cost T X <= _)%nat);
    revert Hc; generalize (@cost T X); intros ? Hc end end.

Lemma item_loop_time a ac t0 tc w0 wc k0 kc i0 ic H hc :
  (cost (extract (extract (extract (extract (extract (item_loop_cost stepsCM a ac) t0 tc) w0 wc) k0 kc) i0 ic) H hc) <= ((50 * Z.to_nat (φ w0) + 50) * Z.to_nat (φ k0) + 60) * Z.to_nat (φ i0) + 10)%nat.
Proof.
  remember ((50 * Z.to_nat (φ w0) + 50) * Z.to_nat (φ k0)) %nat as GR eqn:EGR.
  unfold item_loop_cost. cbn.
  match goal with |- context [@cost ?T (?G a ac t0 tc w0 wc k0 kc i0 ic H hc)] =>
    assert (HG : forall m t0 tc i0 ic H hc, (Z.to_nat (φ i0) <= m)%nat ->
       (cost (G a ac t0 tc w0 wc k0 kc i0 ic H hc) <= (GR + 60) * m + 10)%nat) end.
  { induction m as [|m IH]; intros t' tc' i' ic' [g] hc' Hm;
      cost_simpl;
      pose proof (bdec_time (0 <? i') (bool_w (0 <? i'))) as HB;
      cost_destruct (bdec (0 <? i')); cost_simpl.
    - exfalso. pose proof (down_lt i' e). lia.
    - lia.
    - pose proof (down_lt i' e) as Hg.
      assert (Hm' : (Z.to_nat (φ (i' - 1)) <= m)%nat) by lia.
      z0 row_loop_cost; z1 row_loop_cost; z2 row_loop_cost; z3 row_loop_cost.
      gen_row. rewrite <- EGR in *.
      z0 item_loop_cost; z1 item_loop_cost; z2 item_loop_cost; z3 item_loop_cost; z4 item_loop_cost.
      match goal with |- context [@cost ?T (?G' a ac ?tt ?ttc w0 wc k0 kc (i' - 1)%uint63 ?w ?h ?e)] =>
        have HI := (IH tt ttc (i' - 1)%uint63 w h e Hm' : (@cost T (G' a ac tt ttc w0 wc k0 kc (i' - 1)%uint63 w h e) <= _)%nat) end.
      nia.
    - lia. }
  match goal with |- context [@cost ?T (?G a ac t0 tc w0 wc k0 kc i0 ic H hc)] =>
    exact (HG _ t0 tc i0 ic H hc (le_n _) : (@cost T (G a ac t0 tc w0 wc k0 kc i0 ic H hc) <= _)%nat) end.
Qed.

Lemma best_loop_time t0 tc w0 wc h0 hc0 k0 kc s0 sc H hc :
  (cost (extract (extract (extract (extract (extract (best_loop_cost stepsCM t0 tc) w0 wc) h0 hc0) k0 kc) s0 sc) H hc) <= 80 * Z.to_nat (φ s0) + 80)%nat.
Proof.
  unfold best_loop_cost. cbn.
  match goal with |- context [@cost ?T (?G t0 tc w0 wc h0 hc0 k0 kc s0 sc H hc)] =>
    assert (HG : forall m s0 sc H hc, (Z.to_nat (φ s0) <= m)%nat ->
       (cost (G t0 tc w0 wc h0 hc0 k0 kc s0 sc H hc) <= 80 * m + 80)%nat) end.
  { induction m as [|m IH]; intros s' sc' [g] hc' Hm.
    all: cost_simpl;
      generalize (array_elems tc (k0 * w0 + s')); generalize (array_elems tc (h0 * w0 + s'));
      destruct (t0.[h0 * w0 + s']); intros w1 w2; [ cbn [orb]; cost_simpl | destruct (t0.[k0 * w0 + s']); cbn [orb]; cost_simpl ].
    all: try lia.
    all: pose proof (bdec_time (0 <? s') (bool_w (0 <? s'))) as HB;
      cost_destruct (bdec (0 <? s')); cost_simpl; try lia.
    - pose proof (down_lt s' e) as Hg.
      assert (Hm' : (Z.to_nat (φ (s' - 1)) <= m)%nat) by lia.
      match goal with |- context [@cost ?T (?G' t0 tc w0 wc h0 hc0 k0 kc (s' - 1)%uint63 ?w ?h ?e)] =>
        have HI := (IH (s' - 1)%uint63 w h e Hm' : (@cost T (G' t0 tc w0 wc h0 hc0 k0 kc (s' - 1)%uint63 w h e) <= _)%nat) end.
      lia. }
  match goal with |- context [@cost ?T (?G t0 tc w0 wc h0 hc0 k0 kc s0 sc H hc)] =>
    exact (HG _ s0 sc H hc (le_n _) : (@cost T (G t0 tc w0 wc h0 hc0 k0 kc s0 sc H hc) <= _)%nat) end.
Qed.

Ltac gen_sum := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (sum_loop_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC =>
    let Hc := fresh "Hsum" in
    have Hc := (sum_loop_time a aC b bC c cC d dC : (@cost T X <= _)%nat);
    revert Hc; generalize (@cost T X); intros ? Hc end end.
Ltac gen_item := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (extract (item_loop_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC =>
    let Hc := fresh "Hitem" in
    have Hc := (item_loop_time a aC b bC c cC d dC e eC f fC : (@cost T X <= _)%nat);
    revert Hc; generalize (@cost T X); intros ? Hc end end.
Ltac gen_best := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (extract (best_loop_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC =>
    let Hc := fresh "Hbest" in
    have Hc := (best_loop_time a aC b bC c cC d dC e eC f fC : (@cost T X <= _)%nat);
    revert Hc; generalize (@cost T X); intros ? Hc end end.

Theorem tugofwar_time : exists c1 c2 : nat,
  forall (weights : list N) (weights_arr : array uint),
  valid_input weights -> repr weights_arr weights ->
  (cost1 tugofwar_cost weights_arr <= c1 * ((size weights_arr + 1) * (size weights_arr + 1) * (sizes weights_arr + 1)) + c2)%nat.
Proof.
  exists 300%nat, 500%nat. intros w a [Hn Hw] Ha.
  pose proof (sizes_eq a w Ha) as ESz.
  remember (300 * ((size a + 1) * (size a + 1) * (sizes a + 1)) + 500)%nat as RHS eqn:ERHS.
  unfold cost1, tugofwar_cost, tugofwar_impl_cost. cost_simpl.
  z0 sum_loop_cost; z1 sum_loop_cost; z2 sum_loop_cost.
  z0 item_loop_cost; z1 item_loop_cost; z2 item_loop_cost; z3 item_loop_cost; z4 item_loop_cost.
  z0 best_loop_cost; z1 best_loop_cost; z2 best_loop_cost; z3 best_loop_cost; z4 best_loop_cost.
  z0 make_cost. z1 make_cost. set_simpl.
  repeat match goal with
  | |- context [cost (extract (extract (make_cost ?a ?b ?c) ?d ?e) ?f ?g)] =>
      change (cost (extract (extract (make_cost a b c) d e) f g)) with 1%nat
  end.
  gen_sum. gen_item. gen_best.
  unfold len in Hn.
  pose proof (repr_length a w Ha) as La.
  pose proof (sum_bound w Hw) as Sb.
  assert (HS : (Z.of_N (sum w) <= 45000)%Z) by lia.
  set (Sint := sum_loop a (length a) 0 (Zwf_well_founded 0 (φ (length a)))) in *.
  assert (ES : (φ Sint) = Z.of_N (sum w)).
  { apply (sum_loop_spec w a Ha HS _ (length a) 0 _ eq_refl).
    - change (PArray.length a) with (PArray.length@{Set} a). lia.
    - change (PArray.length a) with (PArray.length@{Set} a).
      replace (Z.to_nat (φ (PArray.length@{Set} a))) with (List.length w) by lia.
      rewrite skipn_all. reflexivity. }
  assert (EN : size a = List.length w).
  { unfold size, size_array. change (PArray.length a) with (PArray.length@{Set} a). lia. }
  assert (E1 : (Z.to_nat (φ (Sint / 2 + 1)) <= sizes a + 1)%nat).
  { rewrite ESz. assert (φ (Sint / 2 + 1) = φ Sint / 2 + 1)%Z by sia. lia. }
  assert (E2 : (Z.to_nat (φ (Sint / 2)) <= sizes a)%nat).
  { rewrite ESz. assert (φ (Sint / 2) = φ Sint / 2)%Z by sia. lia. }
  assert (E3 : (Z.to_nat (φ (length a - length a / 2)) <= size a)%nat).
  { rewrite EN. change (PArray.length a) with (PArray.length@{Set} a).
    assert (φ (PArray.length@{Set} a - PArray.length@{Set} a / 2) = φ (PArray.length@{Set} a) - φ (PArray.length@{Set} a) / 2)%Z by sia.
    lia. }
  assert (E4 : (Z.to_nat (φ (length a)) = size a)%nat) by reflexivity.
  rewrite E4 in Hsum, Hitem.
  revert Hsum Hitem Hbest E1 E2 E3.
  generalize (Z.to_nat (φ (Sint / 2 + 1))) (Z.to_nat (φ (Sint / 2))) (Z.to_nat (φ (length a - length a / 2))).
  intros x1 x2 x3 Hsum Hitem Hbest E1 E2 E3.
  clear - Hsum Hitem Hbest E1 E2 E3 ERHS.
  subst RHS. nia.
Qed.
