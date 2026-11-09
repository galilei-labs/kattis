(* Correctness proofs for tugofwar_implem.v. *)
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
   the code. *)

From Tugofwar.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Bool.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

From Tugofwar Require Export tugofwar_implem.
Open Scope uint63_scope.
Open Scope array_scope.


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

Definition tugofwar_correct : forall (w : list N) (x : array uint),
  valid_input w -> repr x w ->
  exists o : N * N, repr (tugofwar x) o /\ tugofwar_spec w o
  := tugofwar_impl_correct.
