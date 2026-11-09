(* Correctness proofs for shortestpath1_implem.v. *)
(* Implementation of shortestpath1 (shortestpath1.spec): Dijkstra's
   algorithm with a binary min-heap (lazy deletion) over a CSR graph.

   Code.
   - CSR: [count_loop] counts the out-degree of every vertex into
     c.[u+1] (c of length n+1), [prefix_loop] turns c into the offsets
     off.[u] = number of edges whose source is < u, and [fill_loop] places
     edge k at slot off.[us k] + (its rank among the edges of source us k),
     through a copy of the offsets used as insertion cursors.
   - Heap: two parallel flat arrays hk (keys) and hv (vertices) of capacity
     m + 1 and a size; [sift_up] / [sift_down] swap linearly (both cells
     are read before the first set).  Lazy deletion: a relaxation pushes
     (new distance, v); a popped vertex is settled only if [done] says it
     is not settled yet.
   - [main] pops, settles, and [scan] relaxes the out-edges of the settled
     vertex; [out_loop] builds the array of options (INF -> None).

   Termination: every loop recurses on an erased [Acc (Zwf 0) _] proof.
   The measure of [main] is size + (sum of the out-degrees of the
   unsettled vertices), a Prop-side quantity: a pop removes one entry, and
   the scan of the edges of u pushes at most deg u entries while u leaves
   the sum.  No nat, no Z in the code. *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.
Open Scope bool_scope.

Unset Lia Cache.

Require Export shortestpath1_implem.
Open Scope uint63_scope.
Open Scope array_scope.
Open Scope bool_scope.


Lemma aget_make : forall (k x i : int), (PArray.make k x).[i] = x.
Proof. intros k x i. exact (get_make int x k i). Qed.

Lemma alength_make : forall (k x : int),
  PArray.length (PArray.make k x) = if k <=? max_length then k else max_length.
Proof. intros k x. exact (length_make int k x). Qed.

Lemma aget_copy : forall (t : array int) (i : int), (PArray.copy t).[i] = t.[i].
Proof. intros t i. exact (get_copy int t i). Qed.

Lemma alength_copy : forall (t : array int), PArray.length (PArray.copy t) = PArray.length t.
Proof. intros t. exact (length_copy int t). Qed.

(* ------------------------------------------------------------------ *)
(* Prop side: the heap                                                 *)
(* ------------------------------------------------------------------ *)

Definition par (j : int) : int := (j - 1) >> 1.

Lemma par_spec : forall j, (0 < (φ j))%Z -> (φ (par j)) = (((φ j) - 1) / 2)%Z.
Proof.
  intros j Hj. unfold par. rewrite lsr1_spec. f_equal. sia.
Qed.

Lemma par_lt : forall j, (0 < (φ j))%Z -> (0 <= (φ (par j)) < (φ j))%Z.
Proof. intros j Hj. rewrite par_spec by exact Hj. sia. Qed.

Lemma par_neq : forall j, (0 < (φ j))%Z -> par j <> j.
Proof.
  intros j Hj E. pose proof (par_lt j Hj) as P. rewrite E in P. lia.
Qed.

Lemma int_neq : forall a b : int, (φ a) <> (φ b) -> a <> b.
Proof. intros a b H E. apply H. rewrite E. reflexivity. Qed.

Lemma int_eq : forall a b : int, (φ a) = (φ b) -> a = b.
Proof. intros a b H. apply to_Z_inj. exact H. Qed.

(* the children of i are 2 i + 1 and 2 i + 2 *)
Lemma par_child : forall i j, (0 < (φ j))%Z ->
  par j = i <-> ((φ j) = 2 * (φ i) + 1 \/ (φ j) = 2 * (φ i) + 2)%Z.
Proof.
  intros i j Hj. split.
  - intros E. assert ((φ (par j)) = (φ i)) by (rewrite E; reflexivity).
    rewrite par_spec in H by exact Hj. pose proof (to_Z_bounded j). lia.
  - intros E. apply int_eq. rewrite par_spec by exact Hj. lia.
Qed.

Definition heap_ok (hk : array int) (sz : int) : Prop :=
  forall j : int, (0 < (φ j) < (φ sz))%Z -> ((φ (hk.[par j])) <= (φ (hk.[j])))%Z.

Definition in_heap (hk hv : array int) (sz : int) (k v : Z) : Prop :=
  exists i : int, ((φ i) < (φ sz))%Z /\ (φ (hk.[i])) = k /\ (φ (hv.[i])) = v.

Lemma heap_min : forall hk sz, heap_ok hk sz ->
  forall j, ((φ j) < (φ sz))%Z -> ((φ (hk.[0])) <= (φ (hk.[j])))%Z.
Proof.
  intros hk sz Hh.
  assert (forall z, forall j, (φ j) = z -> ((φ j) < (φ sz))%Z -> ((φ (hk.[0])) <= (φ (hk.[j])))%Z);
    [| intros j; apply (H (φ j)); reflexivity].
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j Hz Hj. pose proof (to_Z_bounded j).
  destruct (Z.eq_dec (φ j) 0) as [E | E].
  - replace j with 0 by (apply int_eq; rewrite E; reflexivity). lia.
  - pose proof (par_lt j ltac:(lia)) as P.
    pose proof (Hh j ltac:(lia)).
    assert ((φ (hk.[0])) <= (φ (hk.[par j])))%Z by (apply (IH (φ (par j))); [unfold Zwf; lia | reflexivity | lia]).
    lia.
Qed.

Lemma eqbP : forall x y : int, Bool.reflect (x = y) (x =? y).
Proof. intros x y. apply Bool.iff_reflect. symmetry. apply eqb_spec. Qed.

Lemma get_swap : forall (t : array int) (a b x : int), a <> b ->
  (a <? PArray.length t) = true -> (b <? PArray.length t) = true ->
  t.[a <- t.[b]].[b <- t.[a]].[x] =
  if x =? b then t.[a] else if x =? a then t.[b] else t.[x].
Proof.
  intros t a b x Hab Ha Hb.
  destruct (eqbP x b) as [E | E].
  - subst x. apply aget_set_same. rewrite alength_set. exact Hb.
  - rewrite aget_set_other by (intros F; apply E; symmetry; exact F).
    destruct (eqbP x a) as [E' | E'].
    + subst x. apply aget_set_same. exact Ha.
    + apply aget_set_other. intros F; apply E'; symmetry; exact F.
Qed.

Lemma in_heap_swap : forall hk hv sz a b, a <> b ->
  ((φ a) < (φ sz))%Z -> ((φ b) < (φ sz))%Z ->
  ((φ sz) <= (φ (PArray.length hk)))%Z -> ((φ sz) <= (φ (PArray.length hv)))%Z ->
  forall k v,
  in_heap (hk.[a <- hk.[b]].[b <- hk.[a]]) (hv.[a <- hv.[b]].[b <- hv.[a]]) sz k v
  <-> in_heap hk hv sz k v.
Proof.
  intros hk hv sz a b Hab Ha Hb Lk Lv k v.
  assert (Ak : (a <? PArray.length hk) = true) by (rewrite ltb_spec; lia).
  assert (Bk : (b <? PArray.length hk) = true) by (rewrite ltb_spec; lia).
  assert (Av : (a <? PArray.length hv) = true) by (rewrite ltb_spec; lia).
  assert (Bv : (b <? PArray.length hv) = true) by (rewrite ltb_spec; lia).
  split; intros (x & Hx & Hk & Hv);
    [ rewrite get_swap in Hk, Hv by assumption | ];
    [ destruct (eqbP x b) as [E | E];
      [ exists a | destruct (eqbP x a) as [E' | E']; [exists b | exists x] ]
    | destruct (eqbP x b) as [E | E];
      [ exists a | destruct (eqbP x a) as [E' | E']; [exists b | exists x] ] ];
    repeat split; try (subst; lia);
    rewrite ?get_swap by assumption; subst;
    repeat match goal with
    | |- context [?p =? ?q] =>
        destruct (eqbP p q); [try (subst; congruence) | try congruence]
    end; try congruence; try assumption.
Qed.

Definition SU (hk : array int) (sz i : int) : Prop :=
  (forall j, (0 < (φ j) < (φ sz))%Z -> j <> i ->
     ((φ (hk.[par j])) <= (φ (hk.[j])))%Z) /\
  ((0 < (φ i))%Z -> forall j, (0 < (φ j) < (φ sz))%Z -> par j = i ->
     ((φ (hk.[par i])) <= (φ (hk.[j])))%Z).

Ltac swap_cases :=
  repeat match goal with
  | |- context [?p =? ?q] => destruct (eqbP p q); subst
  end.

Lemma sift_up_spec : forall sz z i hk hv H, (φ i) = z ->
  PArray.length hk = PArray.length hv ->
  ((φ sz) <= (φ (PArray.length hk)))%Z -> ((φ i) < (φ sz))%Z ->
  SU hk sz i ->
  PArray.length (fst (sift_up hk hv i H)) = PArray.length hk /\
  PArray.length (snd (sift_up hk hv i H)) = PArray.length hv /\
  heap_ok (fst (sift_up hk hv i H)) sz /\
  (forall k v, in_heap (fst (sift_up hk hv i H)) (snd (sift_up hk hv i H)) sz k v
               <-> in_heap hk hv sz k v).
Proof.
  intros sz z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i hk hv H Hz Lhv Lsz Hi [Ha Hb].
  destruct H as [H]. cbn [sift_up].
  destruct (bdec (0 <? i)) as [Hi0 | Hi0].
  - pose proof Hi0 as Hi0'. rewrite ltb_spec in Hi0'. change (φ 0) with 0%Z in Hi0'.
    pose proof (par_lt i Hi0') as Pi. fold (par i).
    destruct (bdec (hk.[i] <? hk.[par i])) as [Hlt | Hge].
    + rewrite ltb_spec in Hlt.
      assert (Hne : i <> par i) by (apply not_eq_sym, par_neq; exact Hi0').
      assert (Ai : (i <? PArray.length hk) = true) by (rewrite ltb_spec; lia).
      assert (Ap : (par i <? PArray.length hk) = true) by (rewrite ltb_spec; lia).
      match goal with |- context [sift_up _ _ _ ?A] => generalize A; intros H' end.
      edestruct (IH (φ (par i)) ltac:(unfold Zwf; lia) (par i)
                  (hk.[i <- hk.[par i]].[par i <- hk.[i]])
                  (hv.[i <- hv.[par i]].[par i <- hv.[i]])
                  H' eq_refl)
        as (L1 & L2 & Hh & Hc);
        [ rewrite !alength_set; exact Lhv
        | rewrite !alength_set; exact Lsz | lia | | ].
      * (* SU at the parent *)
        split.
        -- intros j Hj Hjp. rewrite !get_swap by assumption.
           pose proof (par_lt j ltac:(lia)) as Pj.
           destruct (eqbP j i) as [-> | Eji].
           ++ destruct (eqbP (par i) (par i)); [| congruence].
              destruct (eqbP i (par i)); [congruence|]. lia.
           ++ destruct (eqbP j (par i)) as [| Ejp]; [congruence|].
              destruct (eqbP (par j) (par i)) as [Epp | Epp].
              ** (* sibling of i *)
                 assert (par j = par i) by exact Epp.
                 pose proof (Ha j Hj Eji). rewrite Epp in H1. lia.
              ** destruct (eqbP (par j) i) as [Epi | Epi].
                 --- (* child of i *)
                     apply Hb; [lia | lia | exact Epi].
                 --- apply Ha; assumption.
        -- intros Hp0 j Hj Hjp. rewrite !get_swap by assumption.
           pose proof (par_lt (par i) Hp0) as Ppp.
           destruct (eqbP (par (par i)) (par i)) as [E|_]; [lia|].
           destruct (eqbP (par (par i)) i) as [E|_]; [lia|].
           assert (Hpp := Ha (par i) ltac:(lia) (not_eq_sym Hne)).
           destruct (eqbP j (par i)) as [E | _].
           { rewrite E in Hjp. exfalso. apply (par_neq (par i) Hp0). exact Hjp. }
           destruct (eqbP j i) as [_ | Eji]; [lia|].
           pose proof (Ha j Hj Eji). rewrite Hjp in H0. lia.
      * split; [rewrite L1, !alength_set; reflexivity|].
        split; [rewrite L2, !alength_set; reflexivity|].
        split; [exact Hh|].
        intros k v. rewrite Hc. apply in_heap_swap; try lia; assumption.
    + simpl. split; [reflexivity|]. split; [reflexivity|]. split; [|tauto].
      intros j Hj. destruct (eqbP j i) as [-> | E].
      * rewrite <- Bool.not_true_iff_false, ltb_spec in Hge. lia.
      * apply Ha; assumption.
  - simpl. split; [reflexivity|]. split; [reflexivity|]. split; [|tauto].
    rewrite <- Bool.not_true_iff_false, ltb_spec in Hi0. change (φ 0) with 0%Z in Hi0.
    intros j Hj. apply Ha; [exact Hj | apply int_neq; lia].
Qed.

Lemma child_spec : forall hk sz i,
  ((φ (i + i + 1)) < (φ sz))%Z -> ((φ i) < (φ (i + i + 1)))%Z ->
  par (child hk sz (i + i + 1)) = i /\
  ((φ (child hk sz (i + i + 1))) < (φ sz))%Z /\
  ((φ i) < (φ (child hk sz (i + i + 1))))%Z /\
  forall j, (0 < (φ j) < (φ sz))%Z -> par j = i ->
    ((φ (hk.[child hk sz (i + i + 1)])) <= (φ (hk.[j])))%Z.
Proof.
  intros hk sz i Hl Hil.
  assert (El : (φ (i + i + 1)) = (2 * (φ i) + 1)%Z) by sia.
  pose proof (to_Z_bounded sz).
  assert (El1 : (φ (i + i + 1 + 1)) = (2 * (φ i) + 2)%Z) by sia.
  assert (Hc : forall j, (0 < (φ j) < (φ sz))%Z -> par j = i ->
                 j = i + i + 1 \/ j = i + i + 1 + 1).
  { intros j Hj E. apply par_child in E; [| lia].
    destruct E as [E | E]; [left | right]; apply int_eq; lia. }
  unfold child.
  destruct (i + i + 1 + 1 <? sz) eqn:E1; simpl.
  - rewrite ltb_spec in E1.
    destruct (hk.[i + i + 1 + 1] <? hk.[i + i + 1]) eqn:E2.
    + rewrite ltb_spec in E2.
      split; [apply par_child; lia|]. split; [lia|]. split; [lia|].
      intros j Hj Ej. destruct (Hc j Hj Ej) as [-> | ->]; lia.
    + rewrite <- Bool.not_true_iff_false, ltb_spec in E2.
      split; [apply par_child; lia|]. split; [lia|]. split; [lia|].
      intros j Hj Ej. destruct (Hc j Hj Ej) as [-> | ->]; lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in E1.
    split; [apply par_child; lia|]. split; [lia|]. split; [lia|].
    intros j Hj Ej. destruct (Hc j Hj Ej) as [-> | ->]; lia.
Qed.

Definition SD (hk : array int) (sz i : int) : Prop :=
  (forall j, (0 < (φ j) < (φ sz))%Z -> par j <> i ->
     ((φ (hk.[par j])) <= (φ (hk.[j])))%Z) /\
  ((0 < (φ i))%Z -> forall j, (0 < (φ j) < (φ sz))%Z -> par j = i ->
     ((φ (hk.[par i])) <= (φ (hk.[j])))%Z).

Lemma sift_down_spec : forall sz z i hk hv H, gap sz i = z ->
  PArray.length hk = PArray.length hv ->
  ((φ sz) <= (φ (PArray.length hk)))%Z ->
  SD hk sz i ->
  PArray.length (fst (sift_down hk hv sz i H)) = PArray.length hk /\
  PArray.length (snd (sift_down hk hv sz i H)) = PArray.length hv /\
  heap_ok (fst (sift_down hk hv sz i H)) sz /\
  (forall k v, in_heap (fst (sift_down hk hv sz i H)) (snd (sift_down hk hv sz i H)) sz k v
               <-> in_heap hk hv sz k v).
Proof.
  intros sz z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i hk hv H Hz Lhv Lsz [Ha Hb].
  pose proof (alength_bound hk) as Bk.
  destruct H as [H]. cbn [sift_down].
  destruct (bdec ((i + i + 1 <? sz) && (i <? i + i + 1))) as [Hl | Hl].
  - pose proof Hl as Hl'. apply andb_prop in Hl'. destruct Hl' as [Hl1 Hl2].
    rewrite ltb_spec in Hl1, Hl2.
    destruct (child_spec hk sz i Hl1 Hl2) as (Pc & Csz & Ic & Cmin).
    set (c := child hk sz (i + i + 1)) in *.
    assert (Hne : i <> c) by (apply int_neq; lia).
    assert (Ai : (i <? PArray.length hk) = true) by (rewrite ltb_spec; lia).
    assert (Ac : (c <? PArray.length hk) = true) by (rewrite ltb_spec; lia).
    assert (Hc0 : (0 < (φ c))%Z) by (pose proof (to_Z_bounded i); lia).
    destruct (bdec (hk.[c] <? hk.[i])) as [Hlt | Hge].
    + rewrite ltb_spec in Hlt.
      match goal with |- context [sift_down _ _ _ _ ?A] => generalize A; intros H' end.
      edestruct (IH (gap sz c) ltac:(unfold Zwf, gap in *; lia) c
                  (hk.[i <- hk.[c]].[c <- hk.[i]])
                  (hv.[i <- hv.[c]].[c <- hv.[i]])
                  H' eq_refl)
        as (L1 & L2 & Hh & Hcn);
        [ rewrite !alength_set; exact Lhv
        | rewrite !alength_set; exact Lsz | | ].
      * split.
        -- intros j Hj Hjc. rewrite !get_swap by assumption.
           pose proof (par_lt j ltac:(lia)) as Pj.
           destruct (eqbP j c) as [-> | Ejc].
           { rewrite Pc. destruct (eqbP i c); [congruence|].
             destruct (eqbP i i); [|congruence]. destruct (eqbP c c); [|congruence]. lia. }
           destruct (eqbP (par j) c) as [| _]; [congruence|].
           destruct (eqbP (par j) i) as [Epi | Epi].
           ++ (* j is a child of i: c or its sibling *)
              destruct (eqbP j i) as [-> | Eji]; [lia|].
              apply Cmin; assumption.
           ++ destruct (eqbP j i) as [-> | Eji].
              ** (* j = i, i > 0 *)
                 apply (Hb ltac:(lia) c); [lia | exact Pc].
              ** apply Ha; assumption.
        -- intros _ j Hj Hjc. rewrite !get_swap by assumption.
           rewrite Pc.
           destruct (eqbP i c) as [|_]; [congruence|].
           destruct (eqbP i i) as [_|]; [|congruence].
           pose proof (par_lt j ltac:(lia)) as Pj.
           destruct (eqbP j c) as [E | _].
           { exfalso. rewrite E in Hjc. exact (par_neq c Hc0 Hjc). }
           destruct (eqbP j i) as [E | _]; [subst j; lia|].
           pose proof (Ha j Hj ltac:(rewrite Hjc; exact (not_eq_sym Hne))) as X.
           rewrite Hjc in X. exact X.
      * split; [rewrite L1, !alength_set; reflexivity|].
        split; [rewrite L2, !alength_set; reflexivity|].
        split; [exact Hh|].
        intros k v. rewrite Hcn. apply in_heap_swap; try lia; try assumption.
    + simpl. split; [reflexivity|]. split; [reflexivity|]. split; [|tauto].
      rewrite <- Bool.not_true_iff_false, ltb_spec in Hge.
      intros j Hj. destruct (eqbP (par j) i) as [E | E].
      * rewrite E. pose proof (Cmin j Hj E). lia.
      * apply Ha; assumption.
  - simpl. split; [reflexivity|]. split; [reflexivity|]. split; [|tauto].
    intros j Hj. destruct (eqbP (par j) i) as [E | E].
    + exfalso. apply par_child in E; [| lia].
      rewrite <- Bool.not_true_iff_false in Hl. apply Hl.
      apply andb_true_intro. rewrite !ltb_spec. sia.
    + apply Ha; assumption.
Qed.

Lemma pop_spec : forall hk hv sz, (0 < (φ sz))%Z ->
  PArray.length hk = PArray.length hv ->
  ((φ sz) <= (φ (PArray.length hk)))%Z -> heap_ok hk sz ->
  PArray.length (fst (pop hk hv sz)) = PArray.length hk /\
  PArray.length (snd (pop hk hv sz)) = PArray.length hv /\
  heap_ok (fst (pop hk hv sz)) (sz - 1) /\
  (forall i, (0 < (φ i) < (φ sz))%Z ->
     in_heap (fst (pop hk hv sz)) (snd (pop hk hv sz)) (sz - 1)
             (φ (hk.[i])) (φ (hv.[i]))) /\
  (forall k v, in_heap (fst (pop hk hv sz)) (snd (pop hk hv sz)) (sz - 1) k v ->
     in_heap hk hv sz k v).
Proof.
  intros hk hv sz Hs Lhv Lsz Hh. unfold pop.
  assert (Es : (φ (sz - 1)) = ((φ sz) - 1)%Z) by sia.
  assert (A0k : (0 <? PArray.length hk) = true) by (rewrite ltb_spec; change (φ 0) with 0%Z; lia).
  assert (A0v : (0 <? PArray.length hv) = true) by (rewrite <- Lhv; exact A0k).
  match goal with |- context [sift_down _ _ _ _ ?A] => generalize A; intros H' end.
  edestruct (sift_down_spec (sz - 1) _ 0 (hk.[0 <- hk.[sz - 1]]) (hv.[0 <- hv.[sz - 1]])
               H' eq_refl) as (L1 & L2 & Hh' & Hc);
    [ rewrite !alength_set; exact Lhv | rewrite alength_set; lia | | ].
  - split.
    + intros j Hj Hj0. rewrite !aget_set_other; [apply Hh; lia | |].
      * apply int_neq. change (φ 0) with 0%Z. lia.
      * intros E. apply Hj0. symmetry. exact E.
    + change (φ 0) with 0%Z. lia.
  - split; [rewrite L1, alength_set; reflexivity|].
    split; [rewrite L2, alength_set; reflexivity|].
    split; [exact Hh'|].
    split.
    + intros i Hi. apply Hc.
      destruct (Z.eq_dec (φ i) ((φ sz) - 1)) as [E | E].
      * exists 0. rewrite !aget_set_same by assumption.
        replace (sz - 1) with i by (apply int_eq; lia).
        change (φ 0) with 0%Z. repeat split; lia.
      * exists i. rewrite !aget_set_other by (apply int_neq; change (φ 0) with 0%Z; lia).
        repeat split; lia.
    + intros k v Hin. apply Hc in Hin. destruct Hin as (x & Hx & Hk & Hv).
      destruct (eqbP 0 x) as [<- | E].
      * rewrite !aget_set_same in Hk, Hv by assumption.
        exists (sz - 1). repeat split; [lia | exact Hk | exact Hv].
      * rewrite !aget_set_other in Hk, Hv by exact E.
        exists x. repeat split; [lia | exact Hk | exact Hv].
Qed.

Lemma push_spec : forall hk hv sz k v,
  PArray.length hk = PArray.length hv ->
  ((φ sz) < (φ (PArray.length hk)))%Z -> heap_ok hk sz ->
  PArray.length (fst (push hk hv sz k v)) = PArray.length hk /\
  PArray.length (snd (push hk hv sz k v)) = PArray.length hv /\
  heap_ok (fst (push hk hv sz k v)) (sz + 1) /\
  (forall k' v', in_heap (fst (push hk hv sz k v)) (snd (push hk hv sz k v)) (sz + 1) k' v'
     <-> in_heap hk hv sz k' v' \/ (k' = (φ k) /\ v' = (φ v))).
Proof.
  intros hk hv sz k v Lhv Lsz Hh. unfold push.
  pose proof (alength_bound hk).
  assert (Es : (φ (sz + 1)) = ((φ sz) + 1)%Z) by sia.
  assert (Ak : (sz <? PArray.length hk) = true) by (rewrite ltb_spec; lia).
  assert (Av : (sz <? PArray.length hv) = true) by (rewrite <- Lhv; exact Ak).
  match goal with |- context [sift_up _ _ _ ?A] => generalize A; intros H' end.
  edestruct (sift_up_spec (sz + 1) _ sz (hk.[sz <- k]) (hv.[sz <- v]) H' eq_refl)
    as (L1 & L2 & Hh' & Hc);
    [ rewrite !alength_set; exact Lhv | rewrite alength_set; lia | lia | | ].
  - split.
    + intros j Hj Hjs. pose proof (par_lt j ltac:(lia)).
      rewrite !aget_set_other; [apply Hh; lia | exact (not_eq_sym Hjs) |].
      apply int_neq. lia.
    + intros Hs0 j Hj E. exfalso. pose proof (par_lt j ltac:(lia)) as P. rewrite E in P. lia.
  - split; [rewrite L1, alength_set; reflexivity|].
    split; [rewrite L2, alength_set; reflexivity|].
    split; [exact Hh'|].
    intros k' v'. rewrite Hc. split.
    + intros (x & Hx & Hk & Hv).
      destruct (eqbP sz x) as [<- | E].
      * right. rewrite !aget_set_same in Hk, Hv by assumption. split; congruence.
      * left. rewrite !aget_set_other in Hk, Hv by exact E.
        exists x. repeat split; [| exact Hk | exact Hv].
        assert ((φ x) <> (φ sz)) by (intros F; apply E; apply int_eq; congruence). lia.
    + intros [(x & Hx & Hk & Hv) | [-> ->]].
      * exists x. rewrite !aget_set_other by (apply int_neq; lia).
        repeat split; [lia | exact Hk | exact Hv].
      * exists sz. rewrite !aget_set_same by assumption. repeat split; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Prop side: sums                                                     *)
(* ------------------------------------------------------------------ *)

Lemma sumf_add : forall f g K,
  sumf (fun v => f v + g v)%Z K = (sumf f K + sumf g K)%Z.
Proof. intros f g K. induction K as [| K IH]; simpl; lia. Qed.

Lemma sumf_ind1 : forall a K, (0 <= a)%Z ->
  sumf (fun v => if (v =? a)%Z then 1 else 0)%Z K
  = if (a <? Z.of_nat K)%Z then 1%Z else 0%Z.
Proof.
  intros a K Ha. induction K as [| K IH]; simpl.
  - destruct (a <? 0)%Z eqn:E; [rewrite Z.ltb_lt in E; lia | reflexivity].
  - rewrite IH.
    destruct (a <? Z.of_nat K)%Z eqn:E1, (Z.of_nat K =? a)%Z eqn:E2,
             (a <? Z.pos (Pos.of_succ_nat K))%Z eqn:E3;
      rewrite ?Z.ltb_lt, ?Z.ltb_ge, ?Z.eqb_eq, ?Z.eqb_neq in *; lia.
Qed.

Lemma sumf_mono : forall f K1 K2, (forall u, 0 <= f u)%Z -> (K1 <= K2)%nat ->
  (sumf f K1 <= sumf f K2)%Z.
Proof.
  intros f K1 K2 Hf HK. induction HK as [| K2 HK IH]; [lia|].
  simpl. specialize (Hf (Z.of_nat K2)). lia.
Qed.

Lemma sumf_bound : forall f K b, (forall u, (0 <= u < Z.of_nat K)%Z -> f u <= b)%Z ->
  (sumf f K <= Z.of_nat K * b)%Z.
Proof.
  intros f K b Hf. induction K as [| K IH]; [simpl; lia|].
  cbn [sumf]. rewrite Nat2Z.inj_succ in *.
  assert (sumf f K <= Z.of_nat K * b)%Z by (apply IH; intros u Hu; apply Hf; lia).
  specialize (Hf (Z.of_nat K) ltac:(lia)). nia.
Qed.

(* ------------------------------------------------------------------ *)
(* Prop side: the CSR construction                                     *)
(* ------------------------------------------------------------------ *)

Section CSR.

Context (us vs ws : list N) (xu xv xw : array int) (n : Z).
Context (Hm : (φ (PArray.length xu)) = Z.of_nat (List.length us)).
Context (Hvl : List.length vs = List.length us) (Hwl : List.length ws = List.length us).
Context (Hxv : (φ (PArray.length xv)) = Z.of_nat (List.length vs))
        (Hxw : (φ (PArray.length xw)) = Z.of_nat (List.length ws)).
Context (HU : forall k : int, ((φ k) < Z.of_nat (List.length us))%Z ->
                (φ (xu.[k])) = Z.of_N (nth (Z.to_nat (φ k)) us 0%N))
        (HV : forall k : int, ((φ k) < Z.of_nat (List.length us))%Z ->
                (φ (xv.[k])) = Z.of_N (nth (Z.to_nat (φ k)) vs 0%N))
        (HW : forall k : int, ((φ k) < Z.of_nat (List.length us))%Z ->
                (φ (xw.[k])) = Z.of_N (nth (Z.to_nat (φ k)) ws 0%N)).
Context (Hend : forall k : nat, (k < List.length us)%nat ->
                  (Z.of_N (nth k us 0%N) < n)%Z).
Context (Hn : (1 <= n <= 10000)%Z) (HM : (Z.of_nat (List.length us) <= 30000)%Z).

Let M := List.length us.
Let U (k : nat) : N := nth k us 0%N.

Fixpoint cnt (k : nat) (u : N) : nat :=
  match k with
  | O => O
  | S k => (cnt k u + if N.eqb (U k) u then 1 else 0)%nat
  end.

Lemma cnt_le : forall k u, (cnt k u <= k)%nat.
Proof. intros k u. induction k; simpl; [lia|]. destruct (N.eqb (U k) u); lia. Qed.

Lemma cnt_mono : forall k1 k2 u, (k1 <= k2)%nat -> (cnt k1 u <= cnt k2 u)%nat.
Proof.
  intros k1 k2 u H. induction H; [lia|]. simpl. lia.
Qed.

Lemma cnt_lt : forall k k2 u, (k < k2)%nat -> U k = u -> (cnt k u < cnt k2 u)%nat.
Proof.
  intros k k2 u Hk Hu. pose proof (cnt_mono (S k) k2 u Hk). simpl in H.
  rewrite Hu, N.eqb_refl in H. lia.
Qed.

Lemma cnt_rank : forall k u r, (r < cnt k u)%nat ->
  exists k', (k' < k)%nat /\ U k' = u /\ cnt k' u = r.
Proof.
  intros k u r. induction k as [| k IH]; simpl; intros H; [lia|].
  destruct (N.eqb (U k) u) eqn:E.
  - destruct (Nat.eq_dec r (cnt k u)) as [-> | Ne].
    + exists k. split; [lia|]. split; [apply N.eqb_eq; exact E | reflexivity].
    + destruct (IH ltac:(lia)) as (k' & H1 & H2 & H3). exists k'. split; [lia | auto].
  - destruct (IH ltac:(lia)) as (k' & H1 & H2 & H3). exists k'. split; [lia | auto].
Qed.

Definition cntZ (k : nat) (v : Z) : Z := Z.of_nat (cnt k (Z.to_N v)).

Lemma sum_cnt : forall k, (k <= M)%nat -> sumf (cntZ k) (Z.to_nat n) = Z.of_nat k.
Proof.
  intros k. induction k as [| k IH]; intros Hk.
  - unfold cntZ. simpl. induction (Z.to_nat n); simpl; [reflexivity|]. lia.
  - pose proof (Hend k ltac:(unfold M in Hk; lia)) as Hk'.
    rewrite (sumf_ext _ (fun v => cntZ k v + (if (v =? Z.of_N (U k))%Z then 1 else 0))%Z).
    + rewrite sumf_add, IH by lia. rewrite sumf_ind1 by lia.
      destruct (Z.of_N (U k) <? Z.of_nat (Z.to_nat n))%Z eqn:E;
        [|rewrite Z.ltb_ge in E; fold (U k) in Hk'; lia]. lia.
    + intros v Hv. unfold cntZ. simpl. rewrite Nat2Z.inj_add. f_equal.
      destruct (N.eqb (U k) (Z.to_N v)) eqn:E1, (v =? Z.of_N (U k))%Z eqn:E2;
        rewrite ?N.eqb_eq, ?N.eqb_neq, ?Z.eqb_eq, ?Z.eqb_neq in *; try reflexivity; lia.
Qed.

Definition P (x : Z) : Z := sumf (cntZ M) (Z.to_nat x).

Lemma cntZ_nonneg : forall k v, (0 <= cntZ k v)%Z.
Proof. intros. unfold cntZ. lia. Qed.

Lemma P_mono : forall x y, (0 <= x <= y)%Z -> (P x <= P y)%Z.
Proof. intros x y H. apply sumf_mono; [apply cntZ_nonneg | lia]. Qed.

Lemma P_succ : forall x, (0 <= x)%Z -> P (x + 1) = (P x + cntZ M x)%Z.
Proof.
  intros x Hx. unfold P. rewrite Z2Nat.inj_add, Nat.add_1_r by lia. simpl.
  rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma P_n : P n = Z.of_nat M.
Proof. apply sum_cnt. lia. Qed.

Lemma P_le : forall x, (0 <= x <= n)%Z -> (0 <= P x <= Z.of_nat M)%Z.
Proof.
  intros x Hx. rewrite <- P_n. split; [| apply P_mono; lia].
  apply sumf_nonneg, cntZ_nonneg.
Qed.

Lemma HU' : forall k : int, ((φ k) < Z.of_nat M)%Z ->
  (0 <= (φ (xu.[k])) < n)%Z /\ Z.to_N (φ (xu.[k])) = U (Z.to_nat (φ k)).
Proof.
  intros k Hk. rewrite HU by exact Hk. pose proof (to_Z_bounded k).
  split; [split; [lia | apply Hend; lia] | apply N2Z.id].
Qed.

(* the counting loop *)
Lemma count_loop_spec : forall z k c H, gap (PArray.length xu) k = z ->
  ((φ k) <= Z.of_nat M)%Z ->
  (φ (PArray.length c)) = (n + 1)%Z ->
  (forall x : int, ((φ x) <= n)%Z ->
     (φ (c.[x])) = if ((φ x) =? 0)%Z then 0%Z else cntZ (Z.to_nat (φ k)) ((φ x) - 1)) ->
  (φ (PArray.length (count_loop xu (PArray.length xu) k c H))) = (n + 1)%Z /\
  (forall x : int, ((φ x) <= n)%Z ->
     (φ ((count_loop xu (PArray.length xu) k c H).[x]))
     = if ((φ x) =? 0)%Z then 0%Z else cntZ M ((φ x) - 1)).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k c H Hz Hk Lc Hc.
  destruct H as [H]. cbn [count_loop].
  destruct (bdec (k <? PArray.length xu)) as [Hk1 | Hk1].
  - pose proof Hk1 as Hk1'. rewrite ltb_spec, Hm in Hk1'.
    destruct (HU' k Hk1') as [Bu Eu].
    pose proof (to_Z_bounded k).
    assert (E1 : (φ (xu.[k] + 1)) = ((φ (xu.[k])) + 1)%Z) by sia.
    assert (A1 : (xu.[k] + 1 <? PArray.length c) = true) by (rewrite ltb_spec; lia).
    match goal with |- context [count_loop _ _ _ _ ?A] => generalize A; intros H' end.
    apply (IH (gap (PArray.length xu) (k + 1))); [unfold Zwf, gap in *; sia | reflexivity | sia | | ].
    + rewrite alength_set. exact Lc.
    + assert (Ek : Z.to_nat (φ (k + 1)) = S (Z.to_nat (φ k))) by sia.
      intros x Hx. rewrite Ek.
      destruct (eqbP (xu.[k] + 1) x) as [<- | Ne].
      * rewrite aget_set_same by exact A1.
        rewrite E1. destruct ((φ (xu.[k])) + 1 =? 0)%Z eqn:E0; [rewrite Z.eqb_eq in E0; lia|].
        rewrite add_spec, Hc by lia. rewrite E1, E0.
        unfold cntZ. simpl.
        replace ((φ (xu.[k])) + 1 - 1)%Z with (φ (xu.[k])) by lia. rewrite Eu.
        rewrite N.eqb_refl. pose proof (cnt_le (Z.to_nat (φ k)) (U (Z.to_nat (φ k)))).
        assert (Z.of_nat (cnt (Z.to_nat (φ k)) (U (Z.to_nat (φ k)))) < 9223372036854775807)%Z by lia.
        change (φ 1) with 1%Z. rewrite Z.mod_small; lia.
      * rewrite aget_set_other by exact Ne. rewrite Hc by exact Hx.
        destruct ((φ x) =? 0)%Z eqn:E0; [reflexivity|].
        unfold cntZ. simpl. destruct (N.eqb (U (Z.to_nat (φ k))) (Z.to_N ((φ x) - 1))) eqn:E2.
        -- exfalso. apply Ne. apply int_eq. rewrite N.eqb_eq in E2. rewrite Z.eqb_neq in E0.
           pose proof (to_Z_bounded x). lia.
        -- lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec, Hm in Hk1.
    split; [exact Lc|]. intros x Hx. rewrite Hc by exact Hx.
    replace (Z.to_nat (φ k)) with M by lia. reflexivity.
Qed.

Context (xn : int) (Hxn : (φ xn) = n).

Lemma prefix_loop_spec : forall z i c H, gap xn i = z ->
  (0 <= (φ i) <= n)%Z ->
  (φ (PArray.length c)) = (n + 1)%Z ->
  (forall x : int, ((φ x) <= n)%Z ->
     (φ (c.[x])) = if ((φ x) <=? (φ i))%Z then P (φ x) else cntZ M ((φ x) - 1)) ->
  (φ (PArray.length (prefix_loop xn i c H))) = (n + 1)%Z /\
 (forall x : int, ((φ x) <= n)%Z -> (φ ((prefix_loop xn i c H).[x])) = P (φ x)).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i c H Hz Hi Lc Hc.
  destruct H as [H]. cbn [prefix_loop].
  destruct (bdec (i <? xn)) as [Hi1 | Hi1].
  - pose proof Hi1 as Hi1'. rewrite ltb_spec, Hxn in Hi1'.
    assert (E1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    assert (A1 : (i + 1 <? PArray.length c) = true) by (rewrite ltb_spec; lia).
    match goal with |- context [prefix_loop _ _ _ ?A] => generalize A; intros H' end.
    apply (IH (gap xn (i + 1))); [unfold Zwf, gap in *; sia | reflexivity | lia | | ].
    + rewrite alength_set. exact Lc.
    + intros x Hx. destruct (eqbP (i + 1) x) as [<- | Ne].
      * rewrite aget_set_same by exact A1.
        rewrite add_spec, (Hc (i + 1)), (Hc i) by lia. rewrite E1.
        rewrite Z.leb_refl.
        destruct ((φ i) + 1 <=? (φ i))%Z eqn:E; [rewrite Z.leb_le in E; lia|].
        replace ((φ i) + 1 - 1)%Z with (φ i) by lia.
        rewrite P_succ by lia. pose proof (P_le ((φ i) + 1) ltac:(lia)).
        rewrite P_succ in H0 by lia.
        pose proof (cntZ_nonneg M (φ i)). pose proof (P_le (φ i) ltac:(lia)).
        rewrite Z.leb_refl. rewrite Z.mod_small; lia.
      * rewrite aget_set_other by exact Ne. rewrite Hc by exact Hx.
        assert ((φ x) <> (φ i) + 1)%Z by (intros F; apply Ne; apply int_eq; lia).
        rewrite E1.
        destruct ((φ x) <=? (φ i))%Z eqn:Ea, ((φ x) <=? (φ i) + 1)%Z eqn:Eb;
          rewrite ?Z.leb_le, ?Z.leb_gt in *; try reflexivity; lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec, Hxn in Hi1.
    split; [exact Lc|]. intros x Hx. rewrite Hc by exact Hx.
    destruct ((φ x) <=? (φ i))%Z eqn:E; [reflexivity | rewrite Z.leb_gt in E; lia].
Qed.

Definition slot (k : nat) : Z := (P (Z.of_N (U k)) + Z.of_nat (cnt k (U k)))%Z.

Lemma cntZ_of_N : forall k (u : N), cntZ k (Z.of_N u) = Z.of_nat (cnt k u).
Proof. intros k u. unfold cntZ. rewrite N2Z.id. reflexivity. Qed.

Lemma slot_range : forall k, (k < M)%nat ->
  (P (Z.of_N (U k)) <= slot k < P (Z.of_N (U k) + 1))%Z /\
 (P (Z.of_N (U k) + 1) <= Z.of_nat M)%Z.
Proof.
  intros k Hk. unfold slot. rewrite P_succ by lia. rewrite cntZ_of_N.
  pose proof (cnt_lt k M (U k) Hk eq_refl).
  pose proof (Hend k Hk). fold (U k) in H0.
  split; [lia|]. pose proof (P_le (Z.of_N (U k) + 1) ltac:(lia)) as X.
  rewrite P_succ, cntZ_of_N in X by lia. lia.
Qed.

Lemma slot_distinct : forall k1 k2, (k1 < k2)%nat -> (k2 < M)%nat -> slot k1 <> slot k2.
Proof.
  intros k1 k2 H12 H2.
  destruct (slot_range k1 ltac:(lia)) as [R1 _]. destruct (slot_range k2 H2) as [R2 _].
  destruct (N.compare_spec (U k1) (U k2)) as [E | E | E].
  - unfold slot. rewrite E. pose proof (cnt_lt k1 k2 (U k2) H12 E). lia.
  - assert (P (Z.of_N (U k1) + 1) <= P (Z.of_N (U k2)))%Z by (apply P_mono; lia). lia.
  - assert (P (Z.of_N (U k2) + 1) <= P (Z.of_N (U k1)))%Z by (apply P_mono; lia). lia.
Qed.

Lemma fill_loop_spec : forall z k pos adj wt H, gap (PArray.length xu) k = z ->
  ((φ k) <= Z.of_nat M)%Z ->
  (φ (PArray.length adj)) = Z.of_nat M -> (φ (PArray.length wt)) = Z.of_nat M ->
  (φ (PArray.length pos)) = (n + 1)%Z ->
  (forall u : int, ((φ u) < n)%Z ->
     (φ (pos.[u])) = (P (φ u) + Z.of_nat (cnt (Z.to_nat (φ k)) (Z.to_N (φ u))))%Z) ->
  (forall k', (k' < Z.to_nat (φ k))%nat ->
     (φ (adj.[of_Z (slot k')])) = Z.of_N (nth k' vs 0%N) /\
    (φ (wt.[of_Z (slot k')])) = Z.of_N (nth k' ws 0%N)) ->
  let r := fill_loop xu xv xw (PArray.length xu) k pos adj wt H in
  (φ (PArray.length (fst r))) = Z.of_nat M /\ (φ (PArray.length (snd r))) = Z.of_nat M /\
 (forall k', (k' < M)%nat ->
     (φ ((fst r).[of_Z (slot k')])) = Z.of_N (nth k' vs 0%N) /\
    (φ ((snd r).[of_Z (slot k')])) = Z.of_N (nth k' ws 0%N)).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k pos adj wt H Hz Hk La Lw Lp Hpos Hsl.
  destruct H as [H]. cbn [fill_loop].
  destruct (bdec (k <? PArray.length xu)) as [Hk1 | Hk1].
  - pose proof Hk1 as Hk1'. rewrite ltb_spec, Hm in Hk1'.
    destruct (HU' k Hk1') as [Bu Eu].
    pose proof (to_Z_bounded k).
    set (K := Z.to_nat (φ k)) in *.
    assert (EK : Z.to_nat (φ (k + 1)) = S K) by (unfold K; sia).
    assert (Hj : (φ (pos.[xu.[k]])) = slot K).
    { rewrite Hpos by lia. rewrite Eu. unfold slot. f_equal. f_equal. rewrite <- Eu. lia. }
    destruct (slot_range K ltac:(unfold K; lia)) as [Rs RM].
    assert (Aa : (pos.[xu.[k]] <? PArray.length adj) = true) by (rewrite ltb_spec; lia).
    assert (Aw : (pos.[xu.[k]] <? PArray.length wt) = true) by (rewrite ltb_spec; lia).
    match goal with |- context [fill_loop _ _ _ _ _ _ _ _ ?A] => generalize A; intros H' end.
    apply (IH (gap (PArray.length xu) (k + 1))); [unfold Zwf, gap in *; sia | reflexivity | sia | | | | | ].
    + rewrite alength_set. exact La.
    + rewrite alength_set. exact Lw.
    + rewrite alength_set. exact Lp.
    + intros u Hu. rewrite EK. simpl.
      destruct (eqbP (xu.[k]) u) as [<- | Ne].
      * rewrite aget_set_same.
        -- rewrite add_spec, Hj. change (φ 1) with 1%Z. rewrite Eu, N.eqb_refl.
           unfold slot. rewrite <- Eu. rewrite Z2N.id by lia.
           rewrite Z.mod_small; [lia|].
           pose proof (P_le (φ (xu.[k])) ltac:(lia)). pose proof (cnt_le K (U K)).
           rewrite Eu. assert (K <= M)%nat by (unfold K; lia). lia.
        -- rewrite ltb_spec. lia.
      * rewrite aget_set_other by exact Ne. rewrite Hpos by exact Hu.
        destruct (N.eqb (U K) (Z.to_N (φ u))) eqn:E.
        -- exfalso. apply Ne. apply int_eq. rewrite N.eqb_eq in E.
           pose proof (to_Z_bounded u). lia.
        -- lia.
    + intros k' Hk'. rewrite EK in Hk'.
      destruct (Nat.eq_dec k' K) as [-> | Ne].
      * replace (of_Z (slot K)) with (pos.[xu.[k]]) by (rewrite <- Hj; symmetry; apply of_to_Z).
        rewrite !aget_set_same by assumption.
        rewrite HV, HW by lia. split; reflexivity.
      * assert (Hd := slot_distinct k' K ltac:(lia) ltac:(unfold K; lia)).
        destruct (slot_range k' ltac:(unfold K in *; lia)) as [Rs' RM'].
        assert (Nj : pos.[xu.[k]] <> of_Z (slot k')).
        { intros F. apply Hd. rewrite <- Hj, F. symmetry. apply of_Z_small.
          assert (0 <= P (Z.of_N (U k')))%Z by (apply sumf_nonneg, cntZ_nonneg).
          lia. }
        rewrite !aget_set_other by exact Nj. apply Hsl. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec, Hm in Hk1.
    simpl. split; [exact La|]. split; [exact Lw|].
    intros k' Hk'. apply Hsl. lia.
Qed.

Lemma P_0 : P 0 = 0%Z.
Proof. reflexivity. Qed.

Lemma csr_build : forall H1 H2 H3,
  let c := count_loop xu (PArray.length xu) 0 (PArray.make (xn + 1) 0) H1 in
  let off := prefix_loop xn 0 c H2 in
  let r := fill_loop xu xv xw (PArray.length xu) 0 (PArray.copy off)
             (PArray.make (PArray.length xu) 0) (PArray.make (PArray.length xu) 0) H3 in
  (φ (PArray.length off)) = (n + 1)%Z /\
  (forall x : int, ((φ x) <= n)%Z -> (φ (off.[x])) = P (φ x)) /\
  (forall u : int, ((φ u) < n)%Z -> forall j : int,
     ((φ (off.[u])) <= (φ j) < (φ (off.[u + 1])))%Z ->
     exists k, (k < M)%nat /\ U k = Z.to_N (φ u) /\
       (φ ((fst r).[j])) = Z.of_N (nth k vs 0%N) /\
       (φ ((snd r).[j])) = Z.of_N (nth k ws 0%N)) /\
  (forall k, (k < M)%nat -> exists j : int,
     ((φ (off.[of_Z (Z.of_N (U k))])) <= (φ j) < (φ (off.[of_Z (Z.of_N (U k)) + 1])))%Z /\
     (φ ((fst r).[j])) = Z.of_N (nth k vs 0%N) /\
     (φ ((snd r).[j])) = Z.of_N (nth k ws 0%N)) /\
  sumf (deg off) (Z.to_nat n) = Z.of_nat M.
Proof.
  intros H1 H2 H3 c off r.
  assert (Ln1 : (φ (xn + 1)) = (n + 1)%Z) by sia.
  assert (Lc0 : (φ (PArray.length (PArray.make (xn + 1) 0))) = (n + 1)%Z).
  { rewrite alength_make. destruct (xn + 1 <=? max_length) eqn:E; [exact Ln1|].
    rewrite <- Bool.not_true_iff_false, leb_spec, max_length_val in E. lia. }
  assert (Z0 : (φ 0) = 0%Z) by reflexivity.
  assert (K0 : ((φ 0) <= Z.of_nat M)%Z) by (rewrite Z0; lia).
  destruct (count_loop_spec (gap (PArray.length xu) 0) 0 (PArray.make (xn + 1) 0) H1
              eq_refl K0 Lc0)
    as [Lc Hc].
  { intros x Hx. rewrite aget_make. change (φ 0) with 0%Z.
    destruct ((φ x) =? 0)%Z; reflexivity. }
  fold c in Lc, Hc.
  assert (K1 : (0 <= (φ 0) <= n)%Z) by (rewrite Z0; lia).
  destruct (prefix_loop_spec (gap xn 0) 0 c H2 eq_refl K1 Lc)
    as [Loff Hoff].
  { intros x Hx. rewrite Hc by exact Hx. change (φ 0) with 0%Z.
    pose proof (to_Z_bounded x).
    destruct ((φ x) =? 0)%Z eqn:E1, ((φ x) <=? 0)%Z eqn:E2;
      rewrite ?Z.eqb_eq, ?Z.eqb_neq, ?Z.leb_le, ?Z.leb_gt in *; try reflexivity; try lia.
    rewrite E1. reflexivity. }
  fold off in Loff, Hoff.
  assert (LM : (φ (PArray.length (PArray.make (PArray.length xu) 0))) = Z.of_nat M).
  { rewrite alength_make. destruct (PArray.length xu <=? max_length) eqn:E; [exact Hm|].
    rewrite <- Bool.not_true_iff_false, leb_spec, max_length_val in E. unfold M in *. lia. }
  assert (Lcp : (φ (PArray.length (PArray.copy off))) = (n + 1)%Z)
    by (rewrite alength_copy; exact Loff).
  destruct (fill_loop_spec (gap (PArray.length xu) 0) 0 (PArray.copy off)
              (PArray.make (PArray.length xu) 0) (PArray.make (PArray.length xu) 0) H3 eq_refl
              K0 LM LM Lcp)
    as (La & Lw & Hsl).
  { intros u Hu. rewrite aget_copy, Hoff by lia. change (φ 0) with 0%Z. simpl. lia. }
  { intros k' Hk'. change (φ 0) with 0%Z in Hk'. simpl in Hk'. lia. }
  fold r in La, Lw, Hsl.
  split; [exact Loff|]. split; [exact Hoff|]. split; [|split].
  - intros u Hu j Hj. pose proof (to_Z_bounded u).
    assert (Eu1 : (φ (u + 1)) = ((φ u) + 1)%Z) by sia.
    rewrite !Hoff in Hj by lia. rewrite Eu1, P_succ in Hj by lia.
    unfold cntZ in Hj.
    destruct (cnt_rank M (Z.to_N (φ u)) (Z.to_nat ((φ j) - P (φ u))) ltac:(lia))
      as (k & Hk & Huk & Hr).
    exists k. split; [exact Hk|]. split; [exact Huk|].
    destruct (Hsl k Hk) as [Ha Hw].
    replace (of_Z (slot k)) with j in Ha, Hw; [split; assumption|].
    apply int_eq. rewrite of_Z_small.
    + unfold slot. rewrite Huk, Hr, Z2N.id by lia. lia.
    + destruct (slot_range k Hk). assert (0 <= P (Z.of_N (U k)))%Z by (apply sumf_nonneg, cntZ_nonneg). lia.
  - intros k Hk. exists (of_Z (slot k)).
    destruct (slot_range k Hk) as [Rs RM].
    assert (0 <= P (Z.of_N (U k)))%Z by (apply sumf_nonneg, cntZ_nonneg).
    assert (Hu : (Z.of_N (U k) < n)%Z) by exact (Hend k Hk).
    assert (E0 : (φ (of_Z (Z.of_N (U k)))) = Z.of_N (U k)) by (apply of_Z_small; lia).
    assert (E1 : (φ (of_Z (Z.of_N (U k)) + 1)) = (Z.of_N (U k) + 1)%Z) by sia.
    rewrite !Hoff by lia. rewrite E0, E1, of_Z_small by lia.
    split; [lia|]. apply Hsl. exact Hk.
  - rewrite (sumf_ext _ (cntZ M)); [apply sum_cnt; lia|].
    intros u Hu. unfold deg.
    rewrite !Hoff by (rewrite of_Z_small; lia). rewrite !of_Z_small by lia.
    rewrite P_succ by lia. pose proof (cntZ_nonneg M u). lia.
Qed.

End CSR.

(* ------------------------------------------------------------------ *)
(* Prop side: Dijkstra                                                 *)
(* ------------------------------------------------------------------ *)

Definition INFZ : Z := 9223372036854775807%Z.

Lemma INF_val : (φ INF) = INFZ.
Proof. reflexivity. Qed.

Definition isdone (done : array int) (v : int) : Prop := (done.[v] =? 0) = false.

Definition vN (v : int) : N := Z.to_N (φ v).

Lemma of_Z_vN : forall v : int, of_Z (Z.of_N (vN v)) = v.
Proof.
  intros v. unfold vN. pose proof (to_Z_bounded v).
  rewrite Z2N.id by lia. apply of_to_Z.
Qed.

Lemma vN_of_Z : forall z : Z, (0 <= z < 9223372036854775808)%Z ->
  vN (of_Z z) = Z.to_N z.
Proof. intros z Hz. unfold vN. rewrite of_Z_small by exact Hz. reflexivity. Qed.

Lemma Z_of_vN : forall v : int, Z.of_N (vN v) = (φ v).
Proof. intros v. unfold vN. pose proof (to_Z_bounded v). lia. Qed.

Lemma isdone_dec : forall done v, {isdone done v} + {~ isdone done v}.
Proof.
  intros done v. unfold isdone. destruct (done.[v] =? 0); [right; discriminate | left; reflexivity].
Qed.

Lemma not_isdone : forall done v, ~ isdone done v -> (done.[v] =? 0) = true.
Proof.
  intros done v H. unfold isdone in H. destruct (done.[v] =? 0); [reflexivity | congruence].
Qed.

Section Dij.

Context (us vs ws : list N) (n m : Z) (s : int) (off adj wt : array int) (cap : int).
Context (Hn : (1 <= n <= 10000)%Z) (Hm : (0 <= m <= 30000)%Z) (Hcap : (φ cap) = (m + 1)%Z).
Context (Hs : ((φ s) < n)%Z).
Context (Hoffl : (φ (PArray.length off)) = (n + 1)%Z).
Context (Hmono : forall u : int, ((φ u) < n)%Z -> ((φ (off.[u])) <= (φ (off.[u + 1])))%Z).
Context (Hsound : forall u : int, ((φ u) < n)%Z -> forall j : int,
   ((φ (off.[u])) <= (φ j) < (φ (off.[u + 1])))%Z ->
   edge us vs ws (vN u) (vN (adj.[j])) (vN (wt.[j]))).
Context (Hcomp : forall u v w, edge us vs ws u v w -> exists j : int,
   ((φ (off.[of_Z (Z.of_N u)])) <= (φ j) < (φ (off.[of_Z (Z.of_N u) + 1])))%Z /\
   vN (adj.[j]) = v /\ vN (wt.[j]) = w).
Context (Hedge : forall u v w, edge us vs ws u v w ->
   (Z.of_N u < n)%Z /\ (Z.of_N v < n)%Z /\ (w <= 1000)%N).

Definition nd (done : array int) : Z :=
  sumf (fun u => if done.[of_Z u] =? 0 then 0%Z else 1%Z) (Z.to_nat n).

Lemma nd_le : forall done, (0 <= nd done <= n)%Z.
Proof.
  intros done. unfold nd. split.
  - apply sumf_nonneg. intros u. destruct (done.[of_Z u] =? 0); lia.
  - transitivity (Z.of_nat (Z.to_nat n) * 1)%Z; [| lia].
    apply sumf_bound. intros u _. destruct (done.[of_Z u] =? 0); lia.
Qed.

Lemma nd_set : forall done u, (φ (PArray.length done)) = n ->
  (u <? PArray.length done) = true -> (done.[u] =? 0) = true ->
  nd (done.[u <- 1]) = (nd done + 1)%Z.
Proof.
  intros done u Ld Hu H0. unfold nd.
  rewrite ltb_spec in Hu. pose proof (to_Z_bounded u).
  match goal with |- sumf ?f ?k = (sumf ?g ?k + _)%Z =>
    assert (E := sumf_update f g k (φ u) ltac:(lia)) end.
  cbv beta in E.
  rewrite of_to_Z, H0, aget_set_same in E by (rewrite ltb_spec; lia).
  change (1 =? 0) with false in E.
  match type of E with ?P -> _ => enough (Hx : P) by (specialize (E Hx); cbn iota in E; lia) end.
  intros v Hv Hne. rewrite aget_set_other; [reflexivity|].
  intros F. apply Hne. rewrite F, of_Z_small by lia. reflexivity.
Qed.

Lemma path_vert : forall v c, path us vs ws (vN s) v c -> (Z.of_N v < n)%Z.
Proof.
  intros v c Hp. induction Hp as [| u v w c Hp IH He].
  - rewrite Z_of_vN. exact Hs.
  - apply (Hedge u v w He).
Qed.

Record Inv (dist done hk hv : array int) (sz : int) : Prop := {
  i_ld : (φ (PArray.length dist)) = n;
  i_ldn : (φ (PArray.length done)) = n;
  i_lhk : PArray.length hk = cap;
  i_lhv : PArray.length hv = cap;
  i_heap : heap_ok hk sz;
  i_s : (φ (dist.[s])) = 0%Z;
  i_path : forall v : int, ((φ v) < n)%Z -> (φ (dist.[v])) <> INFZ ->
    path us vs ws (vN s) (vN v) (vN (dist.[v]));
  i_bound : forall v : int, ((φ v) < n)%Z -> (φ (dist.[v])) <> INFZ ->
    ((φ (dist.[v])) <= 1000 * nd done)%Z;
  i_done : forall v : int, ((φ v) < n)%Z -> isdone done v ->
    (φ (dist.[v])) <> INFZ /\
    forall c, path us vs ws (vN s) (vN v) c -> ((φ (dist.[v])) <= Z.of_N c)%Z;
  i_relax : forall v : int, ((φ v) < n)%Z -> isdone done v ->
    forall v' w, edge us vs ws (vN v) v' w ->
    ((φ (dist.[of_Z (Z.of_N v')])) <= (φ (dist.[v])) + Z.of_N w)%Z;
  i_front : forall v : int, ((φ v) < n)%Z -> ~ isdone done v -> (φ (dist.[v])) <> INFZ ->
    in_heap hk hv sz (φ (dist.[v])) (φ v);
  i_entries : forall k v, in_heap hk hv sz k v ->
    (0 <= v < n)%Z /\ ((φ (dist.[of_Z v])) <= k)%Z /\ (k <= 1000 * nd done)%Z;
  i_cap : ((φ sz) + pot off done <= m + 1)%Z
}.

Lemma frontier : forall dist done hk hv sz, Inv dist done hk hv sz ->
  forall v c, path us vs ws (vN s) v c ->
  (isdone done (of_Z (Z.of_N v)) /\ ((φ (dist.[of_Z (Z.of_N v)])) <= Z.of_N c)%Z) \/
  (exists y : int, ((φ y) < n)%Z /\ ~ isdone done y /\ (φ (dist.[y])) <> INFZ /\
                   ((φ (dist.[y])) <= Z.of_N c)%Z).
Proof.
  intros dist done hk hv sz I v c Hp.
  induction Hp as [| u v w c Hp IH He].
  - rewrite of_Z_vN. destruct (isdone_dec done s) as [D | D].
    + left. split; [exact D|].
      apply (i_done _ _ _ _ _ I s Hs D). constructor.
    + right. exists s. rewrite (i_s _ _ _ _ _ I). split; [exact Hs|].
      split; [exact D|]. unfold INFZ. lia.
  - pose proof (path_vert u c Hp) as Hu.
    destruct (Hedge u v w He) as (_ & Hv & Hw).
    destruct IH as [[D Hc] | (y & Hy & Dy & Fy & Cy)].
    + set (x := of_Z (Z.of_N u)) in *.
      assert (Ex : (φ x) = Z.of_N u) by (apply of_Z_small; lia).
      assert (Ux : vN x = u) by (unfold vN; rewrite Ex; lia).
      assert (R := i_relax _ _ _ _ _ I x ltac:(lia) D v w ltac:(rewrite Ux; exact He)).
      destruct (i_done _ _ _ _ _ I x ltac:(lia) D) as [Fx _].
      pose proof (i_bound _ _ _ _ _ I x ltac:(lia) Fx).
      pose proof (nd_le done).
      destruct (isdone_dec done (of_Z (Z.of_N v))) as [Dv | Dv].
      * left. split; [exact Dv | lia].
      * right. exists (of_Z (Z.of_N v)).
        rewrite of_Z_small by lia. split; [lia|]. split; [exact Dv|].
        unfold INFZ. lia.
    + right. exists y. split; [exact Hy|]. split; [exact Dy|]. split; [exact Fy | lia].
Qed.

Lemma inv_final : forall dist done hk hv sz, Inv dist done hk hv sz -> (φ sz) = 0%Z ->
  forall v : int, ((φ v) < n)%Z ->
  ((φ (dist.[v])) <> INFZ -> shortest_distance us vs ws (vN s) (vN v) (vN (dist.[v]))) /\
  ((φ (dist.[v])) = INFZ -> ~ reachable us vs ws (vN s) (vN v)).
Proof.
  intros dist done hk hv sz I H0 v Hv. split.
  - intros F. destruct (isdone_dec done v) as [D | D].
    + split; [exact (i_path _ _ _ _ _ I v Hv F)|].
      intros c' Hc'. destruct (i_done _ _ _ _ _ I v Hv D) as [_ Hm'].
      specialize (Hm' c' Hc'). unfold vN. lia.
    + exfalso. destruct (i_front _ _ _ _ _ I v Hv D F) as (i & Hi & _).
      rewrite H0 in Hi. pose proof (to_Z_bounded i). lia.
  - intros F [c Hc]. destruct (frontier _ _ _ _ _ I _ _ Hc) as [[D _] | (y & Hy & Dy & Fy & _)].
    + rewrite of_Z_vN in D. destruct (i_done _ _ _ _ _ I v Hv D) as [F' _]. contradiction.
    + destruct (i_front _ _ _ _ _ I y Hy Dy Fy) as (i & Hi & _).
      rewrite H0 in Hi. pose proof (to_Z_bounded i). lia.
Qed.

(* the vertex at the root, when unsettled, is at its shortest distance *)
Lemma settle : forall dist done hk hv sz, Inv dist done hk hv sz -> (0 < (φ sz))%Z ->
  ((φ (hv.[0])) < n)%Z -> ~ isdone done (hv.[0]) ->
  (φ (dist.[hv.[0]])) = (φ (hk.[0])) /\ (φ (dist.[hv.[0]])) <> INFZ /\
  ((φ (hk.[0])) <= 1000 * nd done)%Z /\
  forall c, path us vs ws (vN s) (vN (hv.[0])) c -> ((φ (dist.[hv.[0]])) <= Z.of_N c)%Z.
Proof.
  intros dist done hk hv sz I Hsz Hu D.
  assert (In0 : in_heap hk hv sz (φ (hk.[0])) (φ (hv.[0]))) by (exists 0; repeat split; lia).
  destruct (i_entries _ _ _ _ _ I _ _ In0) as (_ & Le & Bd).
  rewrite of_to_Z in Le. pose proof (nd_le done).
  assert (F : (φ (dist.[hv.[0]])) <> INFZ) by (unfold INFZ; lia).
  destruct (i_front _ _ _ _ _ I _ Hu D F) as (i & Hi & Hk & _).
  pose proof (heap_min hk sz (i_heap _ _ _ _ _ I) i Hi).
  assert (E : (φ (dist.[hv.[0]])) = (φ (hk.[0]))) by lia.
  split; [exact E|]. split; [exact F|]. split; [exact Bd|].
  intros c Hc. destruct (frontier _ _ _ _ _ I _ _ Hc) as [[D' _] | (y & Hy & Dy & Fy & Cy)].
  - rewrite of_Z_vN in D'. contradiction.
  - destruct (i_front _ _ _ _ _ I y Hy Dy Fy) as (i' & Hi' & Hk' & _).
    pose proof (heap_min hk sz (i_heap _ _ _ _ _ I) i' Hi'). lia.
Qed.

Record SInv (done : array int) (u du : int) (dist hk hv : array int) (sz j : int)
  : Prop := {
  s_ld : (φ (PArray.length dist)) = n;
  s_ldn : (φ (PArray.length done)) = n;
  s_lhk : PArray.length hk = cap;
  s_lhv : PArray.length hv = cap;
  s_heap : heap_ok hk sz;
  s_s : (φ (dist.[s])) = 0%Z;
  s_path : forall v : int, ((φ v) < n)%Z -> (φ (dist.[v])) <> INFZ ->
    path us vs ws (vN s) (vN v) (vN (dist.[v]));
  s_bound : forall v : int, ((φ v) < n)%Z -> (φ (dist.[v])) <> INFZ ->
    ((φ (dist.[v])) <= 1000 * nd done)%Z;
  s_done : forall v : int, ((φ v) < n)%Z -> isdone done v ->
    (φ (dist.[v])) <> INFZ /\
    forall c, path us vs ws (vN s) (vN v) c -> ((φ (dist.[v])) <= Z.of_N c)%Z;
  s_relax : forall v : int, ((φ v) < n)%Z -> isdone done v -> v <> u ->
    forall v' w, edge us vs ws (vN v) v' w ->
    ((φ (dist.[of_Z (Z.of_N v')])) <= (φ (dist.[v])) + Z.of_N w)%Z;
  s_front : forall v : int, ((φ v) < n)%Z -> ~ isdone done v -> (φ (dist.[v])) <> INFZ ->
    in_heap hk hv sz (φ (dist.[v])) (φ v);
  s_entries : forall k v, in_heap hk hv sz k v ->
    (0 <= v < n)%Z /\ ((φ (dist.[of_Z v])) <= k)%Z /\ (k <= 1000 * nd done)%Z;
  s_u : ((φ u) < n)%Z;
  s_ud : isdone done u;
  s_du : (φ (dist.[u])) = (φ du);
  s_dub : ((φ du) + 1000 <= 1000 * nd done)%Z;
  s_j : ((φ (off.[u])) <= (φ j) <= (φ (off.[u + 1])))%Z;
  s_scanned : forall j' : int, ((φ (off.[u])) <= (φ j') < (φ j))%Z ->
    ((φ (dist.[adj.[j']])) <= (φ du) + (φ (wt.[j'])))%Z;
  s_cap : ((φ sz) + ((φ (off.[u + 1])) - (φ j)) + pot off done <= m)%Z
}.

Lemma scan_spec : forall done u du z j dist hk hv sz H,
  gap (off.[u + 1]) j = z ->
  SInv done u du dist hk hv sz j ->
  SInv done u du (st_dist (scan adj wt du (off.[u + 1]) j dist hk hv sz H))
                 (st_hk (scan adj wt du (off.[u + 1]) j dist hk hv sz H))
                 (st_hv (scan adj wt du (off.[u + 1]) j dist hk hv sz H))
                 (st_sz (scan adj wt du (off.[u + 1]) j dist hk hv sz H))
                 (off.[u + 1]).
Proof.
  intros done u du z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j dist hk hv sz H Hz S.
  destruct H as [H]. cbn [scan].
  destruct (bdec (j <? off.[u + 1])) as [Hj | Hj].
  - pose proof Hj as Hj'. rewrite ltb_spec in Hj'.
    destruct S as [Ld Ldn Lhk Lhv Hh S0 S1 SB S2 S3 S4 S5 Su Sud Sdu Sdub SJ SS SC].
    assert (Ej := Hsound u Su j ltac:(lia)).
    destruct (Hedge _ _ _ Ej) as (_ & Hv & Hw).
    rewrite Z_of_vN in Hv.
    assert (Hw' : ((φ (wt.[j])) <= 1000)%Z) by (unfold vN in Hw; lia).
    pose proof (nd_le done).
    pose proof (to_Z_bounded du). pose proof (to_Z_bounded (wt.[j])).
    pose proof (to_Z_bounded (adj.[j])). pose proof (to_Z_bounded j).
    assert (End : (φ (du + wt.[j])) = ((φ du) + (φ (wt.[j])))%Z) by sia.
    assert (Hj1 : (φ (j + 1)) = ((φ j) + 1)%Z) by sia.
    pose proof (pot_nonneg off done).
    set (v := adj.[j]) in *. set (w := wt.[j]) in *.
    destruct (bdec (du + w <? dist.[v])) as [Hlt | Hge].
    + rewrite ltb_spec, End in Hlt.
      assert (Nv : ~ isdone done v).
      { intros Dv. destruct (S2 v Hv Dv) as [_ Hmin].
        assert (Fu : (φ (dist.[u])) <> INFZ) by (unfold INFZ; lia).
        pose proof (path_step us vs ws (vN s) (vN u) (vN v) (vN w) (vN (dist.[u]))
                      (S1 u Su Fu) Ej) as Pv.
        specialize (Hmin _ Pv). unfold vN in Hmin. lia. }
      assert (Nvu : v <> u) by (intros E; apply Nv; rewrite E; exact Sud).
      assert (Nvs : v <> s) by (intros E; rewrite E, S0 in Hlt; lia).
      assert (Hcap' : ((φ sz) < (φ (PArray.length hk)))%Z) by (rewrite Lhk, Hcap; lia).
      destruct (push_spec hk hv sz (du + w) v ltac:(rewrite Lhk, Lhv; reflexivity) Hcap' Hh)
        as (L1 & L2 & Hh' & Hin).
      destruct (push hk hv sz (du + w) v) as [hk' hv'] eqn:Ep. simpl in L1, L2, Hh', Hin.
      cbn beta iota zeta.
      match goal with |- context [scan _ _ _ _ _ _ _ _ _ ?A] => generalize A; intros H' end.
      assert (Avd : (v <? PArray.length dist) = true) by (rewrite ltb_spec, Ld; lia).
      assert (Esz : (φ (sz + 1)) = ((φ sz) + 1)%Z) by sia.
      apply (IH (gap (off.[u + 1]) (j + 1))); [unfold Zwf, gap in *; lia | reflexivity |].
      assert (Dget : forall x, (dist.[v <- du + w]).[x] = if x =? v then du + w else dist.[x]).
      { intros x. destruct (eqbP x v) as [-> | Ne];
          [apply aget_set_same; exact Avd
          | apply aget_set_other; intros E; apply Ne; symmetry; exact E]. }
      assert (Dle : forall x : int, ((φ ((dist.[v <- (du + w)%uint63]).[x])) <= (φ (dist.[x])))%Z)
        by (intros x; rewrite Dget; destruct (eqbP x v) as [-> | _]; lia).
      constructor.
      * rewrite alength_set; exact Ld.
      * exact Ldn.
      * rewrite L1; exact Lhk.
      * rewrite L2; exact Lhv.
      * exact Hh'.
      * rewrite Dget. destruct (eqbP s v) as [E|_]; [congruence | exact S0].
      * intros x Hx Fx. rewrite Dget in *. destruct (eqbP x v) as [-> | Ne].
        -- replace (vN (du + w)) with (vN (dist.[u]) + vN w)%N.
           ++ apply path_step with (from_node := vN u); [apply S1; [exact Su | unfold INFZ; lia] | exact Ej].
           ++ unfold vN. rewrite End, Sdu. lia.
        -- apply S1; assumption.
      * intros x Hx Fx. rewrite Dget in *. destruct (eqbP x v) as [-> | Ne];
          [lia | apply SB; assumption].
      * intros x Hx Dx. rewrite Dget. destruct (eqbP x v) as [-> | Ne];
          [contradiction | apply S2; assumption].
      * intros x Hx Dx Nxu v' w' E'. rewrite (Dget x). destruct (eqbP x v) as [-> | Ne];
          [contradiction|].
        pose proof (Dle (of_Z (Z.of_N v'))). pose proof (S3 x Hx Dx Nxu v' w' E'). lia.
      * intros x Hx Dx Fx. apply Hin. rewrite Dget in *. destruct (eqbP x v) as [-> | Ne].
        -- right. split; reflexivity.
        -- left. apply S4; assumption.
      * intros k x Hk. apply Hin in Hk. destruct Hk as [Hk | [-> ->]].
        -- destruct (S5 k x Hk) as (Hx & Hdx & Hb). split; [exact Hx|]. split; [|exact Hb].
           pose proof (Dle (of_Z x)). lia.
        -- split; [lia|]. rewrite of_to_Z, Dget.
           destruct (eqbP v v); [|congruence]. split; lia.
      * exact Su.
      * exact Sud.
      * rewrite Dget. destruct (eqbP u v) as [E | _]; [congruence | exact Sdu].
      * exact Sdub.
      * lia.
      * intros j' Hj''. destruct (Z.eq_dec (φ j') (φ j)) as [E | E].
        -- replace j' with j by (apply int_eq; lia). fold v w. rewrite Dget.
           destruct (eqbP v v); [|congruence]. lia.
        -- pose proof (Dle (adj.[j'])). pose proof (SS j' ltac:(lia)). lia.
      * lia.
    + rewrite <- Bool.not_true_iff_false, ltb_spec, End in Hge.
      match goal with |- context [scan _ _ _ _ _ _ _ _ _ ?A] => generalize A; intros H' end.
      apply (IH (gap (off.[u + 1]) (j + 1))); [unfold Zwf, gap in *; lia | reflexivity |].
      constructor; try assumption.
      * lia.
      * intros j' Hj''. destruct (Z.eq_dec (φ j') (φ j)) as [E | E].
        -- replace j' with j by (apply int_eq; lia). fold v w. lia.
        -- apply SS. lia.
      * lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hj. simpl.
    assert (E : j = off.[u + 1]) by (apply int_eq; pose proof (s_j _ _ _ _ _ _ _ _ S); lia).
    rewrite <- E. exact S.
Qed.

Lemma done_set_get : forall (done : array int) (u x : int),
  (u <? PArray.length done) = true ->
  ((done.[u <- 1]).[x] =? 0) = if x =? u then false else (done.[x] =? 0).
Proof.
  intros done u x Hu. destruct (eqbP x u) as [-> | Ne].
  - rewrite aget_set_same by exact Hu. reflexivity.
  - rewrite aget_set_other by (intros E; apply Ne; symmetry; exact E). reflexivity.
Qed.

Lemma start_scan : forall dist done hk hv sz,
  Inv dist done hk hv sz -> (0 < (φ sz))%Z ->
  ((hv.[0] <? PArray.length done) && (done.[hv.[0]] =? 0)) = true ->
  SInv (done.[hv.[0] <- 1]) (hv.[0]) (dist.[hv.[0]]) dist
       (fst (pop hk hv sz)) (snd (pop hk hv sz)) (sz - 1) (off.[hv.[0]]).
Proof.
  intros dist done hk hv sz I Hsz Hu.
  apply andb_prop in Hu. destruct Hu as [Hu H0].
  pose proof Hu as Hu'. rewrite ltb_spec, (i_ldn _ _ _ _ _ I) in Hu'.
  set (u := hv.[0]) in *.
  assert (Nu : ~ isdone done u) by (unfold isdone; congruence).
  destruct (settle _ _ _ _ _ I Hsz Hu' Nu) as (Eu & Fu & Bu & Mu).
  fold u in Eu, Fu, Bu, Mu.
  destruct (pop_spec hk hv sz Hsz ltac:(rewrite (i_lhk _ _ _ _ _ I), (i_lhv _ _ _ _ _ I); reflexivity)
              ltac:(rewrite (i_lhk _ _ _ _ _ I), Hcap; pose proof (i_cap _ _ _ _ _ I);
                    pose proof (pot_nonneg off done); lia)
              (i_heap _ _ _ _ _ I))
    as (L1 & L2 & Hh1 & Hkeep & Hsub).
  pose proof (nd_set done u (i_ldn _ _ _ _ _ I) Hu H0) as Nd.
  pose proof (pot_set_done off done u Hu H0) as Pd.
  pose proof (nd_le done).
  assert (Esz : (φ (sz - 1)) = ((φ sz) - 1)%Z) by sia.
  assert (Hdeg : deg off (φ u) = ((φ (off.[u + 1])) - (φ (off.[u])))%Z).
  { unfold deg. rewrite of_to_Z. pose proof (to_Z_bounded u).
    replace (of_Z ((φ u) + 1)) with (u + 1).
    - pose proof (Hmono u Hu'). lia.
    - apply int_eq. rewrite of_Z_small by lia. sia. }
  assert (Dget : forall x, isdone (done.[u <- 1]) x <-> x = u \/ isdone done x).
  { intros x. unfold isdone. rewrite done_set_get by exact Hu.
    destruct (eqbP x u); [tauto|]. split; [tauto|]. intros [E|E]; [contradiction | exact E]. }
  constructor.
  - exact (i_ld _ _ _ _ _ I).
  - rewrite alength_set. exact (i_ldn _ _ _ _ _ I).
  - rewrite L1. exact (i_lhk _ _ _ _ _ I).
  - rewrite L2. exact (i_lhv _ _ _ _ _ I).
  - exact Hh1.
  - exact (i_s _ _ _ _ _ I).
  - exact (i_path _ _ _ _ _ I).
  - intros x Hx Fx. rewrite Nd. pose proof (i_bound _ _ _ _ _ I x Hx Fx). lia.
  - intros x Hx Dx. apply Dget in Dx. destruct Dx as [-> | Dx].
    + split; [exact Fu | exact Mu].
    + exact (i_done _ _ _ _ _ I x Hx Dx).
  - intros x Hx Dx Nxu. apply Dget in Dx. destruct Dx as [-> | Dx]; [contradiction|].
    exact (i_relax _ _ _ _ _ I x Hx Dx).
  - intros x Hx Dx Fx.
    assert (Nxu : x <> u) by (intros E; apply Dx, Dget; left; exact E).
    assert (Dx' : ~ isdone done x) by (intros E; apply Dx, Dget; right; exact E).
    destruct (i_front _ _ _ _ _ I x Hx Dx' Fx) as (i & Hi & Hk & Hv).
    destruct (Z.eq_dec (φ i) 0) as [E | E].
    + exfalso. apply Nxu. apply int_eq. rewrite <- Hv.
      replace i with 0 by (apply int_eq; rewrite E; reflexivity). reflexivity.
    + rewrite <- Hk, <- Hv. apply Hkeep. pose proof (to_Z_bounded i). lia.
  - intros k x Hin. apply Hsub in Hin.
    destruct (i_entries _ _ _ _ _ I k x Hin) as (Hx & Hd & Hb). lia.
  - exact Hu'.
  - apply Dget. left. reflexivity.
  - reflexivity.
  - rewrite Nd. lia.
  - pose proof (Hmono u Hu'). lia.
  - intros j' Hj'. lia.
  - rewrite Pd, Hdeg, Esz. pose proof (i_cap _ _ _ _ _ I). lia.
Qed.

Lemma end_scan : forall done u du dist hk hv sz,
  SInv done u du dist hk hv sz (off.[u + 1]) -> Inv dist done hk hv sz.
Proof.
  intros done u du dist hk hv sz S.
  destruct S as [Ld Ldn Lhk Lhv Hh S0 S1 SB S2 S3 S4 S5 Su Sud Sdu Sdub SJ SS SC].
  constructor; try assumption.
  - intros x Hx Dx v' w E'. destruct (eqbP x u) as [-> | Nxu].
    + destruct (Hcomp _ _ _ E') as (j & Hj & Ev & Ew).
      rewrite of_Z_vN in Hj. rewrite <- Ev, <- Ew, of_Z_vN, Z_of_vN, Sdu.
      apply SS. exact Hj.
    + apply S3; assumption.
  - pose proof (pot_nonneg off done). lia.
Qed.

Lemma skip_inv : forall dist done hk hv sz,
  Inv dist done hk hv sz -> (0 < (φ sz))%Z ->
  ((hv.[0] <? PArray.length done) && (done.[hv.[0]] =? 0)) = false ->
  Inv dist done (fst (pop hk hv sz)) (snd (pop hk hv sz)) (sz - 1).
Proof.
  intros dist done hk hv sz I Hsz Hu.
  destruct (pop_spec hk hv sz Hsz ltac:(rewrite (i_lhk _ _ _ _ _ I), (i_lhv _ _ _ _ _ I); reflexivity)
              ltac:(rewrite (i_lhk _ _ _ _ _ I), Hcap; pose proof (i_cap _ _ _ _ _ I);
                    pose proof (pot_nonneg off done); lia)
              (i_heap _ _ _ _ _ I))
    as (L1 & L2 & Hh1 & Hkeep & Hsub).
  assert (Esz : (φ (sz - 1)) = ((φ sz) - 1)%Z) by sia.
  destruct I as [Ld Ldn Lhk Lhv Hh I0 I1 IB I2 I3 I4 I5 IC].
  constructor; try assumption.
  - rewrite L1. exact Lhk.
  - rewrite L2. exact Lhv.
  - intros x Hx Dx Fx.
    destruct (I4 x Hx Dx Fx) as (i & Hi & Hk & Hv).
    destruct (Z.eq_dec (φ i) 0) as [E | E].
    + exfalso. replace i with 0 in Hv by (apply int_eq; rewrite E; reflexivity).
      assert (hv.[0] = x) by (apply int_eq; exact Hv). subst x.
      rewrite <- Bool.not_true_iff_false in Hu. apply Hu. apply andb_true_intro. split.
      * rewrite ltb_spec, Ldn. exact Hx.
      * apply not_isdone. exact Dx.
    + rewrite <- Hk, <- Hv. apply Hkeep. pose proof (to_Z_bounded i). lia.
  - intros k x Hin. apply Hsub in Hin. exact (I5 k x Hin).
  - lia.
Qed.

Definition final_ok (d : array int) : Prop :=
  (φ (PArray.length d)) = n /\
  forall v : int, ((φ v) < n)%Z ->
  ((φ (d.[v])) <> INFZ -> shortest_distance us vs ws (vN s) (vN v) (vN (d.[v]))) /\
  ((φ (d.[v])) = INFZ -> ~ reachable us vs ws (vN s) (vN v)).

Lemma main_spec : forall z done st H, mu off done (st_sz st) = z ->
  Inv (st_dist st) done (st_hk st) (st_hv st) (st_sz st) ->
  final_ok (main off adj wt done st H).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros done [dist hk hv sz] H Hz I. simpl in I.
  destruct H as [H]. cbn [main st_sz st_hk st_hv st_dist] in *.
  destruct (bdec (0 <? sz)) as [Hs0 | Hs0].
  - pose proof Hs0 as Hs0'. rewrite ltb_spec in Hs0'. change (φ 0) with 0%Z in Hs0'.
    pose proof (start_scan dist done hk hv sz I Hs0') as Hstart.
    pose proof (skip_inv dist done hk hv sz I Hs0') as Hskip.
    destruct (pop hk hv sz) as [hk1 hv1] eqn:Ep. simpl in Hstart, Hskip.
    destruct (bdec ((hv.[0] <? PArray.length done) && (done.[hv.[0]] =? 0))) as [Hu | Hu].
    + match goal with |- context [main _ _ _ _ _ ?A] => generalize A; intros H' end.
      specialize (Hstart Hu).
      match type of H' with Acc _ (mu _ _ (st_sz ?r)) =>
        apply (IH (mu off (done.[hv.[0] <- 1]) (st_sz r))) end.
      * rewrite <- Hz. apply main_step1 with (st := mkSt dist hk hv sz); [exact Hs0 | exact Hu |].
        apply scan_size.
      * reflexivity.
      * eapply end_scan. apply scan_spec with (z := gap (off.[hv.[0] + 1]) (off.[hv.[0]]));
          [reflexivity | exact Hstart].
    + match goal with |- context [main _ _ _ _ _ ?A] => generalize A; intros H' end.
      apply (IH (mu off done (sz - 1))).
      * rewrite <- Hz. apply main_step2 with (st := mkSt dist hk hv sz). exact Hs0.
      * reflexivity.
      * simpl. exact (Hskip Hu).
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hs0. change (φ 0) with 0%Z in Hs0.
    assert (E0 : (φ sz) = 0%Z) by (pose proof (to_Z_bounded sz); lia).
    split; [exact (i_ld _ _ _ _ _ I)|].
    exact (inv_final _ _ _ _ _ I E0).
Qed.

End Dij.

(* ------------------------------------------------------------------ *)
(* Prop side: the output                                               *)
(* ------------------------------------------------------------------ *)

Definition cell (dist : array int) (x : int) : option int :=
  if dist.[x] =? INF then None else Some (dist.[x]).

Lemma oget_set_same : forall (t : array (option int)) (i : int) (b : option int),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same (option int) t i b H). Qed.

Lemma oget_set_other : forall (t : array (option int)) (i j : int) (b : option int),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other (option int) t i j b H). Qed.

Lemma olength_set : forall (t : array (option int)) (i : int) (b : option int),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set (option int) t i b). Qed.

Lemma olength_make : forall (k : int) (x : option int),
  PArray.length (PArray.make k x) = if k <=? max_length then k else max_length.
Proof. intros k x. exact (length_make (option int) k x). Qed.

Lemma out_loop_spec : forall dist xn z v out H, gap xn v = z ->
  ((φ v) <= (φ xn))%Z -> PArray.length out = xn ->
  (forall x : int, ((φ x) < (φ v))%Z -> out.[x] = cell dist x) ->
  PArray.length (out_loop dist xn v out H) = xn /\
  forall x : int, ((φ x) < (φ xn))%Z -> (out_loop dist xn v out H).[x] = cell dist x.
Proof.
  intros dist xn z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros v out H Hz Hv Lo Ho.
  destruct H as [H]. cbn [out_loop].
  destruct (bdec (v <? xn)) as [Hv1 | Hv1].
  - pose proof Hv1 as Hv1'. rewrite ltb_spec in Hv1'.
    assert (E1 : (φ (v + 1)) = ((φ v) + 1)%Z) by sia.
    match goal with |- context [out_loop _ _ _ _ ?A] => generalize A; intros H' end.
    apply (IH (gap xn (v + 1))); [unfold Zwf, gap in *; lia | reflexivity | lia | | ].
    + rewrite olength_set. exact Lo.
    + intros x Hx. destruct (eqbP v x) as [<- | Ne].
      * rewrite oget_set_same by (rewrite Lo; exact Hv1). reflexivity.
      * rewrite oget_set_other by exact Ne. apply Ho.
        assert ((φ x) <> (φ v)) by (intros F; apply Ne; apply int_eq; lia). lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hv1.
    split; [exact Lo|]. intros x Hx. apply Ho. lia.
Qed.

Lemma repr_uint_array : forall (x : array uint) (l : list N), repr x l ->
  (φ (PArray.length x)) = Z.of_nat (List.length l) /\
  forall k : int, ((φ k) < Z.of_nat (List.length l))%Z ->
    (φ (x.[k])) = Z.of_N (nth (Z.to_nat (φ k)) l 0%N).
Proof.
  intros x l [Hl Hc]. split; [symmetry; exact Hl|].
  intros k Hk. destruct (Hc (Z.to_nat (φ k)) ltac:(lia)) as (m & Hm & Hr).
  unfold repr, repr_uint in Hr.
  assert (Ek : of_Z (Z.of_nat (Z.to_nat (φ k))) = k)
    by (rewrite Z2Nat.id by (pose proof (to_Z_bounded k); lia); apply of_to_Z).
  rewrite Ek in Hr.
  assert (Hr' : Z.to_N (φ (x.[k])) = m) by exact Hr.
  rewrite (nth_error_nth l (Z.to_nat (φ k)) 0%N Hm). pose proof (to_Z_bounded (x.[k])). lia.
Qed.

Definition out_list (dist : array int) (K : nat) : list (option N) :=
  map (fun k => option_map vN (cell dist (of_Z (Z.of_nat k)))) (seq 0 K).

Lemma nth_out_list : forall dist K k, (k < K)%nat ->
  nth k (out_list dist K) None = option_map vN (cell dist (of_Z (Z.of_nat k))).
Proof.
  intros dist K k Hk. unfold out_list.
  rewrite (nth_indep _ None (option_map vN (cell dist (of_Z (Z.of_nat 0)))))
    by (rewrite length_map, length_seq; lia).
  rewrite (map_nth (fun k => option_map vN (cell dist (of_Z (Z.of_nat k))))), seq_nth by lia.
  reflexivity.
Qed.

Lemma repr_out : forall (out : array (option uint)) (dist : array int) (L : int),
  PArray.length out = L ->
  (forall x : int, ((φ x) < (φ L))%Z -> out.[x] = cell dist x) ->
  repr out (out_list dist (Z.to_nat (φ L))).
Proof.
  intros out dist L Hl0 Hc0.
  assert (Hl : PArray.length@{repr_array.u0} out = L) by exact Hl0.
  assert (Hc : forall x : int, ((φ x) < (φ L))%Z -> PArray.get@{repr_array.u0} out x = cell dist x)
    by exact Hc0.
  clear Hl0 Hc0.
  split.
  - unfold out_list. rewrite length_map, length_seq, Hl. pose proof (to_Z_bounded L). lia.
  - intros k Hk. unfold out_list in Hk. rewrite length_map, length_seq in Hk.
    exists (option_map vN (cell dist (of_Z (Z.of_nat k)))). split.
    + unfold out_list. rewrite nth_error_map, nth_error_seq.
      destruct (Nat.ltb_spec k (Z.to_nat (φ L))); [reflexivity | lia].
    + rewrite Hc by (rewrite of_Z_small; pose proof (to_Z_bounded L); lia).
      unfold cell. destruct (_ =? INF); simpl; [exact I | reflexivity].
Qed.

Lemma Forall_nth_N : forall (P0 : N -> Prop) (l : list N) k,
  Forall P0 l -> (k < List.length l)%nat -> P0 (nth k l 0%N).
Proof.
  intros P0 l k H Hk. rewrite Forall_forall in H. apply H. apply nth_In. exact Hk.
Qed.

Lemma dijkstra_impl_correct :
  forall (n : N) (us vs ws : list N) (s : N)
         (xn : uint) (xu xv xw : array uint) (xs : uint),
  valid_input n us vs ws s ->
  repr xn n -> repr xu us -> repr xv vs -> repr xw ws -> repr xs s ->
  exists d : list (option N),
    repr (dijkstra_impl xn xu xv xw xs) d /\ dijkstra_spec n us vs ws s d.
Proof.
  intros n us vs ws s xn xu xv xw xs Hv Rn Ru Rv Rw Rs.
  destruct Hv as [Vn Vm Vvl Vwl Vend Vw Vs].
  unfold repr, repr_uint in Rn, Rs.
  destruct (repr_uint_array xu us Ru) as [Lu HU].
  destruct (repr_uint_array xv vs Rv) as [Lv HV].
  destruct (repr_uint_array xw ws Rw) as [Lw HW].
  clear Ru Rv Rw.
  unfold len in *.
  set (M := List.length us) in *.
  assert (Hvl : List.length vs = M) by lia.
  assert (Hwl : List.length ws = M) by lia.
  set (nZ := Z.of_N n).
  pose proof (to_Z_bounded xn). pose proof (to_Z_bounded xs).
  assert (Hxn : (φ xn) = nZ) by (unfold nZ; lia).
  assert (Hxs : vN xs = s) by (unfold vN; lia).
  assert (Hn : (1 <= nZ <= 10000)%Z) by (unfold nZ; lia).
  assert (HM : (Z.of_nat M <= 30000)%Z) by lia.
  assert (Hs : ((φ xs) < nZ)%Z) by (unfold vertex in Vs; unfold nZ; lia).
  assert (Hend : forall k, (k < M)%nat -> (Z.of_N (nth k us 0%N) < nZ)%Z).
  { intros k Hk. destruct (Vend (N.of_nat k) ltac:(unfold edge_index, len; lia)) as [A _].
    unfold vertex, get_list_N in A. rewrite Nat2N.id in A. unfold nZ. lia. }
  unfold dijkstra_impl. cbv zeta.
  pose proof (csr_build us vs ws xu xv xw nZ Lu Hvl Hwl HU
                (fun k Hk => HV k ltac:(lia)) (fun k Hk => HW k ltac:(lia))
                Hend Hn HM xn Hxn
                (Zwf_well_founded 0 _) (Zwf_well_founded 0 _) (Zwf_well_founded 0 _)) as C.
  cbv zeta in C.
  set (off := prefix_loop xn 0 _ _) in *.
  destruct C as (Loff & Hoff & Hsnd & Hcmp & Hsum).
  match goal with |- context [fill_loop ?a ?b ?c ?d ?e ?f ?g ?h ?i] =>
    destruct (fill_loop a b c d e f g h i) as [adj wt] eqn:Ef end.
  change (@PArray.length uint xu) with (@PArray.length int xu) in Ef.
  rewrite Ef in Hsnd, Hcmp. simpl in Hsnd, Hcmp.
  change (@PArray.length uint xu) with (@PArray.length int xu).
  set (cap := PArray.length xu + 1) in *.
  assert (Hcap : (φ cap) = (Z.of_nat M + 1)%Z) by (unfold cap; sia).
  assert (Hmono : forall u : int, ((φ u) < nZ)%Z -> ((φ (off.[u])) <= (φ (off.[u + 1])))%Z).
  { intros u Hu. pose proof (to_Z_bounded u).
    assert (Eu1 : (φ (u + 1)) = ((φ u) + 1)%Z) by sia.
    rewrite !Hoff by lia. rewrite Eu1. apply (P_mono us vs ws xu xv xw Hvl Hwl). lia. }
  assert (Hsound : forall u : int, ((φ u) < nZ)%Z -> forall j : int,
     ((φ (off.[u])) <= (φ j) < (φ (off.[u + 1])))%Z ->
     edge us vs ws (vN u) (vN (adj.[j])) (vN (wt.[j]))).
  { intros u Hu j Hj. destruct (Hsnd u Hu j Hj) as (k & Hk & Huk & Ha & Hw).
    exists (N.of_nat k). unfold edge_index, len, get_list_N. rewrite Nat2N.id.
    split; [lia|]. unfold vN. split; [exact Huk|]. split; lia. }
  assert (Hcomp : forall u v w, edge us vs ws u v w -> exists j : int,
     ((φ (off.[of_Z (Z.of_N u)])) <= (φ j) < (φ (off.[of_Z (Z.of_N u) + 1])))%Z /\
     vN (adj.[j]) = v /\ vN (wt.[j]) = w).
  { intros u v w (k & Hk & Eu & Ev & Ew). unfold edge_index, len, get_list_N in *.
    destruct (Hcmp (N.to_nat k) ltac:(lia)) as (j & Hj & Ha & Hw).
    exists j. rewrite Eu in Hj. split; [exact Hj|]. unfold vN. split; lia. }
  assert (Hedge : forall u v w, edge us vs ws u v w ->
            (Z.of_N u < nZ)%Z /\ (Z.of_N v < nZ)%Z /\ (w <= 1000)%N).
  { intros u v w (k & Hk & Eu & Ev & Ew). destruct (Vend k Hk) as [A B].
    unfold vertex in A, B. rewrite Eu in A. rewrite Ev in B.
    split; [unfold nZ; lia|]. split; [unfold nZ; lia|].
    rewrite <- Ew. unfold get_list_N. apply (Forall_nth_N (fun w => (w <= 1000)%N)); [exact Vw|].
    unfold edge_index, len in Hk. lia. }
  assert (Lmk : forall k x : int, ((φ k) <= 4194303)%Z -> PArray.length (PArray.make k x) = k).
  { intros k x Hk. rewrite alength_make.
    destruct (k <=? max_length) eqn:E; [reflexivity|].
    rewrite <- Bool.not_true_iff_false, leb_spec, max_length_val in E. lia. }
  set (dist0 := (PArray.make xn INF).[xs <- 0]).
  set (done0 := PArray.make xn 0).
  set (hk0 := PArray.make cap 0).
  set (hv0 := (PArray.make cap 0).[0 <- xs]).
  assert (Ld0 : PArray.length dist0 = xn) by (unfold dist0; rewrite alength_set; apply Lmk; lia).
  assert (D0 : forall x, dist0.[x] = if x =? xs then 0 else INF).
  { intros x. unfold dist0. destruct (eqbP x xs) as [-> | Ne].
    - apply aget_set_same. rewrite ltb_spec, Lmk by lia. lia.
    - rewrite aget_set_other by (intros E; apply Ne; symmetry; exact E). apply aget_make. }
  assert (Lc0 : PArray.length (PArray.make cap 0) = cap) by (apply Lmk; lia).
  assert (A0 : (0 <? PArray.length (PArray.make cap 0)) = true)
    by (rewrite ltb_spec, Lc0; change (φ 0) with 0%Z; lia).
  pose proof (nd_le nZ xs off cap Hn done0) as Nd0.
  assert (I0 : Inv us vs ws nZ (Z.of_nat M) xs off cap dist0 done0 hk0 hv0 1).
  { constructor.
    - rewrite Ld0. exact Hxn.
    - unfold done0. rewrite Lmk by lia. exact Hxn.
    - unfold hk0. exact Lc0.
    - unfold hv0. rewrite alength_set. exact Lc0.
    - intros j Hj. change (φ 1) with 1%Z in Hj. lia.
    - rewrite D0. destruct (eqbP xs xs); [reflexivity | congruence].
    - intros v Hv Fv. rewrite D0 in *. destruct (eqbP v xs) as [-> | Ne];
        [| exfalso; apply Fv; reflexivity].
      change (vN 0) with 0%N. constructor.
    - intros v Hv Fv. rewrite D0 in *. destruct (eqbP v xs) as [-> | Ne];
        [| exfalso; apply Fv; reflexivity].
      change (φ 0) with 0%Z. lia.
    - intros v Hv Dv. exfalso. unfold isdone, done0 in Dv. rewrite aget_make in Dv. discriminate.
    - intros v Hv Dv. exfalso. unfold isdone, done0 in Dv. rewrite aget_make in Dv. discriminate.
    - intros v Hv Dv Fv. rewrite D0 in *. destruct (eqbP v xs) as [-> | Ne];
        [| exfalso; apply Fv; reflexivity].
      exists 0. unfold hk0, hv0. rewrite aget_make, aget_set_same by exact A0.
      change (φ 0) with 0%Z. change (φ 1) with 1%Z. repeat split; lia.
    - intros k v (i & Hi & Hk & Hvv). change (φ 1) with 1%Z in Hi.
      assert (i = 0) by (apply int_eq; pose proof (to_Z_bounded i); change (φ 0) with 0%Z; lia).
      subst i. unfold hk0, hv0 in *. rewrite aget_make in Hk. rewrite aget_set_same in Hvv by exact A0.
      subst k v. rewrite of_to_Z, D0. destruct (eqbP xs xs); [|congruence].
      change (φ 0) with 0%Z. lia.
    - unfold pot, done0. rewrite Lmk by lia.
      rewrite (sumf_ext _ (deg off)).
      + rewrite Hxn, Hsum. change (φ 1) with 1%Z. lia.
      + intros u _. rewrite aget_make. reflexivity. }
  pose proof (main_spec us vs ws nZ (Z.of_nat M) xs off adj wt cap Hn ltac:(lia) Hcap Hs
                Hmono Hsound Hcomp Hedge _ done0 (mkSt dist0 hk0 hv0 1)
                (Zwf_well_founded 0 _) eq_refl I0) as F.
  set (dist_f := main off adj wt done0 (mkSt dist0 hk0 hv0 1) _) in *.
  destruct F as [Lf Hf].
  destruct (out_loop_spec dist_f xn _ 0 (PArray.make xn None) (Zwf_well_founded 0 _) eq_refl
              ltac:(change (φ 0) with 0%Z; lia)
              ltac:(rewrite olength_make; destruct (xn <=? max_length) eqn:E; [reflexivity|];
                    rewrite <- Bool.not_true_iff_false, leb_spec, max_length_val in E; lia)
              ltac:(intros x Hx; change (φ 0) with 0%Z in Hx; pose proof (to_Z_bounded x); lia))
    as [Lo Ho].
  exists (out_list dist_f (Z.to_nat (φ xn))). split.
  - apply repr_out; assumption.
  - split.
    + unfold len, out_list. rewrite length_map, length_seq. unfold nZ in Hxn. lia.
    + intros v Hv. unfold vertex in Hv. unfold get_list_option.
      rewrite nth_out_list by (unfold nZ in Hxn; lia).
      set (x := of_Z (Z.of_nat (N.to_nat v))).
      assert (Ex : (φ x) = Z.of_N v) by (unfold x; rewrite of_Z_small; lia).
      assert (Vx : vN x = v) by (unfold vN; lia).
      destruct (Hf x ltac:(unfold nZ; lia)) as [Hsome Hnone].
      unfold cell. destruct (eqbP (dist_f.[x]) INF) as [E | E]; simpl.
      * rewrite <- Vx, <- Hxs. apply Hnone. rewrite E. reflexivity.
      * rewrite <- Vx, <- Hxs. apply Hsome. intros F. apply E. apply int_eq. rewrite F. reflexivity.
Qed.

Definition dijkstra_correct :
  forall (n : N) (us vs ws : list N) (s : N)
         (xn : uint) (xu xv xw : array uint) (xs : uint),
  valid_input n us vs ws s ->
  repr xn n -> repr xu us -> repr xv vs -> repr xw ws -> repr xs s ->
  exists d : list (option N),
    repr (dijkstra xn xu xv xw xs) d /\ dijkstra_spec n us vs ws s d
  := dijkstra_impl_correct.
