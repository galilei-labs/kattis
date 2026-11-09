(* Correctness proofs for booking_implem.v. *)
(* Implementation of booking (booking.spec): interval partitioning by
   sorting.  Every date-time becomes a minute count in O(1) (closed-form
   Gregorian day count); each booking gives an arrival key and a release
   key (departure + c), refined by sub-slots so that zero-length bookings
   (c = 0, arrival = departure) are handled as the spec's [compatible]
   says, and so that all keys of one array are distinct; both flat arrays
   are sorted in place by quicksort (Lomuto, middle pivot); one linear
   two-pointer sweep returns max_p (p + 1 - #{releases <= A[p]}).
   Termination: erased Acc (Zwf 0) proofs on Z measures, as in the
   template.  See README.md, "Implementation". *)

From Booking.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Permutation Sorted.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

From Booking Require Export booking_implem.
Open Scope uint63_scope.
Open Scope array_scope.


(* ------------------------------------------------------------------ *)
(* Generic list lemmas                                                 *)
(* ------------------------------------------------------------------ *)

Lemma filter_length_perm : forall {A} (f : A -> bool) (l l' : list A),
  Permutation l l' -> List.length (filter f l) = List.length (filter f l').
Proof.
  intros A f l l' HP. induction HP; simpl.
  - reflexivity.
  - destruct (f x); simpl; lia.
  - destruct (f x), (f y); simpl; lia.
  - lia.
Qed.

Lemma filter_length_ext : forall {A} (f g : A -> bool) (l : list A),
  (forall x, In x l -> f x = g x) -> List.length (filter f l) = List.length (filter g l).
Proof.
  intros A f g l H. induction l as [| x l IH]; simpl; [reflexivity|].
  rewrite (H x (or_introl eq_refl)).
  destruct (g x); simpl; rewrite IH by (intros y Hy; apply H; right; exact Hy); reflexivity.
Qed.

Lemma filter_length_split : forall {A} (f g : A -> bool) (l : list A),
  List.length (filter f l) = (List.length (filter (fun x => f x && g x) l)
                         + List.length (filter (fun x => f x && negb (g x)) l))%nat.
Proof.
  intros A f g l. induction l as [| x l IH]; simpl; [reflexivity|].
  destruct (f x), (g x); simpl; lia.
Qed.

Lemma NoDup_remove_any : forall (l : list nat) x, NoDup l -> NoDup (remove Nat.eq_dec x l).
Proof.
  intros l x H. induction H as [| y l Hy H IH]; simpl; [constructor|].
  destruct (Nat.eq_dec x y); [exact IH|].
  constructor; [|exact IH]. intro F. apply Hy. exact (proj1 (in_remove _ _ _ _ F)).
Qed.

Lemma NoDup_map_inj : forall {A B} (f : A -> B) (l : list A),
  NoDup l -> (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup (map f l).
Proof.
  intros A B f l H Hi. apply NoDup_map_NoDup_ForallPairs; [|exact H].
  intros x y Hx Hy. apply Hi; assumption.
Qed.

(* a list of fewer than k colors misses some color below k *)
Lemma free_color : forall (l : list N) (k : N),
  (List.length l < N.to_nat k)%nat -> exists c, (c < k)%N /\ ~ In c l.
Proof.
  intros l k Hl.
  set (cands := filter (fun c => negb (existsb (fun x => N.eqb x (N.of_nat c)) l))
                       (seq 0 (N.to_nat k))).
  destruct cands as [| c rest] eqn:E.
  - exfalso.
    assert (Hinc : incl (seq 0 (N.to_nat k)) (map N.to_nat l)).
    { intros c Hc.
      destruct (existsb (fun x => N.eqb x (N.of_nat c)) l) eqn:Ex.
      + apply existsb_exists in Ex. destruct Ex as [x [Hx Hxe]].
        apply N.eqb_eq in Hxe. apply in_map_iff. exists x. split; [lia|exact Hx].
      + assert (In c cands) by (apply filter_In; rewrite Ex; split; [exact Hc|reflexivity]).
        rewrite E in H. destruct H. }
    pose proof (NoDup_incl_length (seq_NoDup _ _) Hinc) as Hle.
    rewrite length_seq, length_map in Hle. lia.
  - assert (Hc : In c cands) by (rewrite E; left; reflexivity).
    apply filter_In in Hc. destruct Hc as [Hc Hn].
    apply in_seq in Hc.
    exists (N.of_nat c). split; [lia|].
    intro F. rewrite Bool.negb_true_iff in Hn.
    assert (existsb (fun x => N.eqb x (N.of_nat c)) l = true)
      by (apply existsb_exists; exists (N.of_nat c); split; [exact F | apply N.eqb_refl]).
    congruence.
Qed.

(* ------------------------------------------------------------------ *)
(* Interval partitioning, on half-open key intervals [al i, rh i)       *)
(* ------------------------------------------------------------------ *)

Section Partition.
  Variables (al rh : nat -> Z).

  Definition conflict (i j : nat) : Prop := (al j < rh i /\ al i < rh j)%Z.

  Definition activeb (t : Z) (j : nat) : bool := ((al j <=? t) && (t <? rh j))%Z.

  Definition cntD (t : Z) (L : list nat) : nat := List.length (filter (activeb t) L).

  Lemma cntD_lower : forall (room : nat -> N) (k : N) (L : list nat),
    NoDup L ->
    (forall i, In i L -> (room i < k)%N) ->
    (forall i j, In i L -> In j L -> i <> j -> room i = room j -> ~ conflict i j) ->
    forall t, (cntD t L <= N.to_nat k)%nat.
  Proof.
    intros room k L HL Hk Hc t. unfold cntD.
    set (L' := filter (activeb t) L).
    assert (HL' : NoDup L') by (apply NoDup_filter; exact HL).
    assert (Hm : NoDup (map (fun i => N.to_nat (room i)) L')).
    { apply NoDup_map_inj; [exact HL'|].
      intros x y Hx Hy Hxy.
      apply filter_In in Hx, Hy. destruct Hx as [Hx Ax], Hy as [Hy Ay].
      destruct (Nat.eq_dec x y) as [|Hne]; [assumption|]. exfalso.
      apply (Hc x y Hx Hy Hne); [lia|].
      unfold activeb in Ax, Ay. apply andb_prop in Ax, Ay.
      destruct Ax as [Ax1 Ax2], Ay as [Ay1 Ay2].
      rewrite Z.leb_le in Ax1, Ay1. rewrite Z.ltb_lt in Ax2, Ay2.
      unfold conflict. lia. }
    assert (Hi : incl (map (fun i => N.to_nat (room i)) L') (seq 0 (N.to_nat k))).
    { intros c Hcm. apply in_map_iff in Hcm. destruct Hcm as [x [Hx Hxin]].
      apply filter_In in Hxin. destruct Hxin as [Hxin _].
      apply in_seq. pose proof (Hk x Hxin). lia. }
    pose proof (NoDup_incl_length Hm Hi) as Hle.
    rewrite length_map, length_seq in Hle. exact Hle.
  Qed.

  Lemma max_exists : forall (L : list nat), L <> [] ->
    exists i, In i L /\ forall j, In j L -> (al j <= al i)%Z.
  Proof.
    intros L. induction L as [| x L IH]; intros Hne; [congruence|].
    destruct L as [| y L'].
    - exists x. split; [left; reflexivity|]. intros j [Hj|[]]. subst. lia.
    - destruct IH as [i [Hi Hmax]]; [discriminate|].
      destruct (Z_le_dec (al x) (al i)).
      + exists i. split; [right; exact Hi|]. intros j [Hj|Hj]; [subst; lia|].
        apply Hmax; exact Hj.
      + exists x. split; [left; reflexivity|]. intros j [Hj|Hj]; [subst; lia|].
        pose proof (Hmax j Hj). lia.
  Qed.

  Lemma cntD_incl : forall t L L', NoDup L' -> incl L' L ->
    (cntD t L' <= cntD t L)%nat.
  Proof.
    intros t L L' Hn Hi. unfold cntD. apply NoDup_incl_length.
    - apply NoDup_filter. exact Hn.
    - intros x Hx. apply filter_In in Hx. apply filter_In. destruct Hx as [Hx Ax].
      split; [apply Hi; exact Hx | exact Ax].
  Qed.

  Lemma cntD_upper : forall (K : N) (n : nat) (L : list nat),
    (List.length L <= n)%nat ->
    NoDup L ->
    (forall i, In i L -> (al i < rh i)%Z) ->
    (forall i, In i L -> (cntD (al i) L <= N.to_nat K)%nat) ->
    exists room : nat -> N,
      (forall i, In i L -> (room i < K)%N) /\
      (forall i j, In i L -> In j L -> i <> j -> room i = room j -> ~ conflict i j).
  Proof.
    intros K n. induction n as [| n IH]; intros L Hlen HL Hnon HK.
    - destruct L; [|simpl in Hlen; lia].
      exists (fun _ => 0%N). split; [intros i Hi; destruct Hi | intros i j Hi; destruct Hi].
    - destruct L as [| x0 L0] eqn:EL.
      + exists (fun _ => 0%N). split; [intros i Hi; destruct Hi | intros i j Hi; destruct Hi].
      + rewrite <- EL in *.
        destruct (max_exists L) as [i [Hi Hmax]]; [rewrite EL; discriminate|].
        set (L' := remove Nat.eq_dec i L).
        assert (HL' : NoDup L') by (apply NoDup_remove_any; exact HL).
        assert (HlenL' : (List.length L' <= n)%nat)
          by (pose proof (remove_length_lt Nat.eq_dec L i Hi); unfold L'; lia).
        assert (Hincl : incl L' L) by (intros y Hy; exact (proj1 (in_remove _ _ _ _ Hy))).
        destruct (IH L' HlenL' HL' (fun j Hj => Hnon j (Hincl j Hj))) as [room' [Hr1 Hr2]].
        { intros j Hj. pose proof (cntD_incl (al j) L L' HL' Hincl).
          pose proof (HK j (Hincl j Hj)). lia. }
        set (C := filter (fun j => ((al j <? rh i) && (al i <? rh j))%Z) L').
        assert (HC : (List.length C < N.to_nat K)%nat).
        { assert (Hsub : incl (i :: C) (filter (activeb (al i)) L)).
          { intros y [Hy|Hy].
            - subst y. apply filter_In. split; [exact Hi|].
              unfold activeb. pose proof (Hnon i Hi).
              apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
            - apply filter_In in Hy. destruct Hy as [Hy Cy].
              apply filter_In. split; [apply Hincl; exact Hy|].
              apply andb_prop in Cy. destruct Cy as [_ Cy]. rewrite Z.ltb_lt in Cy.
              unfold activeb. pose proof (Hmax y (Hincl y Hy)).
              apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
          assert (Hnd : NoDup (i :: C)).
          { constructor.
            - intro F. apply filter_In in F. destruct F as [F _].
              exact (remove_In _ _ _ F).
            - apply NoDup_filter. exact HL'. }
          pose proof (NoDup_incl_length Hnd Hsub) as Hle.
          pose proof (HK i Hi) as Hk. unfold cntD in Hk. simpl in Hle. lia. }
        destruct (free_color (map room' C) K ltac:(rewrite length_map; exact HC))
          as [c [Hck Hcn]].
        exists (fun j => if Nat.eqb j i then c else room' j).
        assert (HinL' : forall j, In j L -> j <> i -> In j L')
          by (intros j Hj Hne; apply in_in_remove; assumption).
        assert (Hfree : forall j, In j L' -> conflict i j -> room' j <> c).
        { intros j Hj Hcf E. apply Hcn. apply in_map_iff. exists j. split; [exact E|].
          apply filter_In. split; [exact Hj|]. destruct Hcf as [H1 H2].
          apply andb_true_intro; split; apply Z.ltb_lt; assumption. }
        split.
        * intros j Hj. destruct (Nat.eqb_spec j i); [exact Hck|].
          apply Hr1. apply HinL'; assumption.
        * intros j1 j2 Hj1 Hj2 Hne Heq.
          destruct (Nat.eqb_spec j1 i) as [E1|E1], (Nat.eqb_spec j2 i) as [E2|E2].
          -- congruence.
          -- subst j1. intro Hcf. apply (Hfree j2 (HinL' j2 Hj2 E2) Hcf). congruence.
          -- subst j2. intro Hcf. apply (Hfree j1 (HinL' j1 Hj1 E1)).
             ++ destruct Hcf as [H1 H2]. split; assumption.
             ++ congruence.
          -- apply Hr2; auto.
  Qed.
End Partition.

(* ------------------------------------------------------------------ *)
(* Uint63 / PArray plumbing                                            *)
(* ------------------------------------------------------------------ *)

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma max_length_val : (φ PArray.max_length) = 4194303%Z.
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

Lemma alength_make : forall (n : int) (b : int),
  PArray.length (PArray.make n b)
  = if n <=? PArray.max_length then n else PArray.max_length.
Proof. intros n b. exact (length_make int n b). Qed.

Lemma alength_bound : forall (t : array int), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length int t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

Lemma phi_of_nat : forall k : nat, (Z.of_nat k < wB)%Z -> (φ (of_Z (Z.of_nat k))) = Z.of_nat k.
Proof.
  intros k Hk. rewrite of_Z_spec. apply Z.mod_small. lia.
Qed.

Lemma phi_neq : forall i j : int, (φ i) <> (φ j) -> i <> j.
Proof. intros i j H E. apply H. rewrite E. reflexivity. Qed.

Lemma part_loop_eq : forall a p hi1 i j H,
  part_loop a p hi1 i j H =
  match bdec (j <? hi1) with
  | left Hj =>
      if a.[j] <? p
      then part_loop (swap a i j) p hi1 (i + 1) (j + 1) (Acc_inv H (dec_step hi1 j Hj))
      else part_loop a p hi1 i (j + 1) (Acc_inv H (dec_step hi1 j Hj))
  | right _ => (a, i)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma qsort_eq : forall a lo hi H,
  qsort a lo hi H =
  match bdec (lo + 1 <? hi) with
  | left _ =>
      let (a1, m) := partition a lo hi in
      match bdec ((lo <=? m) && (m <? hi)) with
      | left Hm =>
          let a2 := qsort a1 lo m (Acc_inv H (dec_left lo hi m Hm)) in
          qsort a2 (m + 1) hi (Acc_inv H (dec_right lo hi m Hm))
      | right _ => a1
      end
  | right _ => a
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Quicksort: proof                                                    *)
(* ------------------------------------------------------------------ *)

Definition view (a : array int) : list Z :=
  map (fun k => (φ (a.[of_Z (Z.of_nat k)]))) (seq 0 (Z.to_nat (φ (PArray.length a)))).

(* b is a rearrangement of a inside [lo, hi) *)
Definition sim (lo hi : int) (a b : array int) : Prop :=
  PArray.length b = PArray.length a /\
  (forall k, ((φ k) < (φ lo) \/ (φ hi) <= (φ k))%Z -> b.[k] = a.[k]) /\
  (forall k, ((φ lo) <= (φ k) < (φ hi))%Z ->
     exists k', ((φ lo) <= (φ k') < (φ hi))%Z /\ b.[k] = a.[k']) /\
  Permutation (view b) (view a).

Lemma sim_refl : forall lo hi a, sim lo hi a a.
Proof.
  intros lo hi a. split; [reflexivity|]. split; [reflexivity|]. split; [|reflexivity].
  intros k Hk. exists k. split; [exact Hk | reflexivity].
Qed.

Lemma sim_trans : forall lo hi a b c, sim lo hi a b -> sim lo hi b c -> sim lo hi a c.
Proof.
  intros lo hi a b c [L1 [O1 [G1 P1]]] [L2 [O2 [G2 P2]]].
  split; [congruence|]. split.
  - intros k Hk. rewrite O2, O1 by exact Hk. reflexivity.
  - split.
    + intros k Hk. destruct (G2 k Hk) as [k' [Hk' E']]. destruct (G1 k' Hk') as [k'' [Hk'' E'']].
      exists k''. split; [exact Hk''|congruence].
    + eapply perm_trans; eassumption.
Qed.

Lemma sim_widen : forall lo hi lo' hi' a b,
  ((φ lo') <= (φ lo))%Z -> ((φ hi) <= (φ hi'))%Z -> sim lo hi a b -> sim lo' hi' a b.
Proof.
  intros lo hi lo' hi' a b H1 H2 [L [O [G P]]].
  split; [exact L|]. split.
  - intros k Hk. apply O. lia.
  - split; [|exact P].
    intros k Hk.
    destruct (Z_lt_le_dec (φ k) (φ lo)) as [Hl|Hl];
      [exists k; split; [lia| apply O; lia]|].
    destruct (Z_lt_le_dec (φ k) (φ hi)) as [Hh|Hh];
      [|exists k; split; [lia| apply O; lia]].
    destruct (G k ltac:(lia)) as [k' [Hk' E]]. exists k'. split; [lia|exact E].
Qed.

Lemma swap_length : forall a i j, PArray.length (swap a i j) = PArray.length a.
Proof. intros. unfold swap. rewrite !alength_set. reflexivity. Qed.

Lemma swap_get : forall a i j k,
  ((φ i) < (φ (PArray.length a)))%Z -> ((φ j) < (φ (PArray.length a)))%Z ->
  (swap a i j).[k] = if k =? j then a.[i] else if k =? i then a.[j] else a.[k].
Proof.
  intros a i j k Hi Hj. unfold swap.
  destruct (k =? j) eqn:Ekj.
  - apply eqb_spec in Ekj. subst k. apply aget_set_same. rewrite alength_set, ltb_spec. exact Hj.
  - apply eqb_false_spec in Ekj. rewrite aget_set_other by congruence.
    destruct (k =? i) eqn:Eki.
    + apply eqb_spec in Eki. subst k. apply aget_set_same. rewrite ltb_spec. exact Hi.
    + apply eqb_false_spec in Eki. apply aget_set_other. congruence.
Qed.

Lemma perm_transpose : forall (n x y : nat), (x < n)%nat -> (y < n)%nat ->
  Permutation (map (fun k => if Nat.eqb k y then x else if Nat.eqb k x then y else k)
                   (seq 0 n)) (seq 0 n).
Proof.
  intros n x y Hx Hy.
  set (tau := fun k : nat => if Nat.eqb k y then x else if Nat.eqb k x then y else k).
  apply NoDup_Permutation.
  - apply NoDup_map_inj; [apply seq_NoDup|].
    intros u v _ _. unfold tau.
    destruct (Nat.eqb_spec u y), (Nat.eqb_spec u x), (Nat.eqb_spec v y), (Nat.eqb_spec v x);
      lia.
  - apply seq_NoDup.
  - intros k. rewrite in_map_iff. split.
    + intros [u [Eu Hu]]. apply in_seq in Hu. apply in_seq. subst k. unfold tau.
      destruct (Nat.eqb_spec u y), (Nat.eqb_spec u x); lia.
    + intros Hk. apply in_seq in Hk. exists (tau k). split.
      * unfold tau. destruct (Nat.eqb_spec k y) as [E1|E1].
        -- subst k. destruct (Nat.eqb_spec x y) as [E2|E2]; [lia|].
           rewrite Nat.eqb_refl. reflexivity.
        -- destruct (Nat.eqb_spec k x) as [E2|E2].
           ++ subst k. rewrite Nat.eqb_refl. reflexivity.
           ++ destruct (Nat.eqb_spec k y); [lia|]. destruct (Nat.eqb_spec k x); [lia|].
              reflexivity.
      * apply in_seq. unfold tau. destruct (Nat.eqb_spec k y), (Nat.eqb_spec k x); lia.
Qed.

Lemma swap_perm : forall a i j,
  ((φ i) < (φ (PArray.length a)))%Z -> ((φ j) < (φ (PArray.length a)))%Z ->
  Permutation (view (swap a i j)) (view a).
Proof.
  intros a i j Hi Hj. unfold view. rewrite swap_length.
  pose proof (alength_bound a) as Hb.
  pose proof (to_Z_bounded i) as Bi. pose proof (to_Z_bounded j) as Bj.
  set (n := Z.to_nat (φ (PArray.length a))).
  set (x := Z.to_nat (φ i)). set (y := Z.to_nat (φ j)).
  set (g := fun k : nat => (φ (a.[of_Z (Z.of_nat k)]))).
  transitivity (map g (map (fun k => if Nat.eqb k y then x else if Nat.eqb k x then y else k)
                         (seq 0 n))).
  - rewrite map_map. apply Permutation_refl'. apply map_ext_in.
    intros k Hk. apply in_seq in Hk. unfold g.
    rewrite swap_get by assumption.
    assert (Hkb : (φ (of_Z (Z.of_nat k))) = Z.of_nat k)
      by (apply phi_of_nat; rewrite wB_val; unfold n in Hk; lia).
    destruct (Nat.eqb_spec k y) as [Ey|Ey].
    + replace (of_Z (Z.of_nat k) =? j) with true.
      2:{ symmetry. apply eqb_spec. apply to_Z_inj. rewrite Hkb. unfold y in Ey. lia. }
      f_equal. f_equal. apply to_Z_inj. rewrite phi_of_nat by (rewrite wB_val; unfold n in Hk; lia).
      unfold x. lia.
    + replace (of_Z (Z.of_nat k) =? j) with false.
      2:{ symmetry. apply eqb_false_spec. apply phi_neq. rewrite Hkb. unfold y in Ey. lia. }
      destruct (Nat.eqb_spec k x) as [Ex|Ex].
      * replace (of_Z (Z.of_nat k) =? i) with true.
        2:{ symmetry. apply eqb_spec. apply to_Z_inj. rewrite Hkb. unfold x in Ex. lia. }
        f_equal. f_equal. apply to_Z_inj.
        rewrite phi_of_nat by (rewrite wB_val; unfold n in Hk; lia). unfold y. lia.
      * replace (of_Z (Z.of_nat k) =? i) with false.
        2:{ symmetry. apply eqb_false_spec. apply phi_neq. rewrite Hkb. unfold x in Ex. lia. }
        reflexivity.
  - apply Permutation_map. apply perm_transpose; unfold x, y, n; lia.
Qed.

Lemma sim_swap : forall lo hi a i j,
  ((φ hi) <= (φ (PArray.length a)))%Z ->
  ((φ lo) <= (φ i) < (φ hi))%Z -> ((φ lo) <= (φ j) < (φ hi))%Z ->
  sim lo hi a (swap a i j).
Proof.
  intros lo hi a i j Hh Hi Hj.
  split; [apply swap_length|]. split.
  - intros k Hk. rewrite swap_get by lia.
    replace (k =? j) with false by (symmetry; apply eqb_false_spec; apply phi_neq; lia).
    replace (k =? i) with false by (symmetry; apply eqb_false_spec; apply phi_neq; lia).
    reflexivity.
  - split.
    + intros k Hk. rewrite swap_get by lia.
      destruct (k =? j); [exists i; split; [lia|reflexivity]|].
      destruct (k =? i); [exists j; split; [lia|reflexivity]|].
      exists k. split; [lia|reflexivity].
    + apply swap_perm; lia.
Qed.

Lemma swap_get_j : forall a i j,
  ((φ i) < (φ (PArray.length a)))%Z -> ((φ j) < (φ (PArray.length a)))%Z ->
  (swap a i j).[j] = a.[i].
Proof. intros. rewrite swap_get by assumption. rewrite eqb_refl. reflexivity. Qed.

Lemma swap_get_i : forall a i j,
  ((φ i) < (φ (PArray.length a)))%Z -> ((φ j) < (φ (PArray.length a)))%Z ->
  (swap a i j).[i] = a.[j].
Proof.
  intros. rewrite swap_get by assumption. destruct (i =? j) eqn:E.
  - apply eqb_spec in E. subst. reflexivity.
  - rewrite eqb_refl. reflexivity.
Qed.

Lemma swap_get_other : forall a i j k,
  ((φ i) < (φ (PArray.length a)))%Z -> ((φ j) < (φ (PArray.length a)))%Z ->
  (φ k) <> (φ i) -> (φ k) <> (φ j) -> (swap a i j).[k] = a.[k].
Proof.
  intros a i j k Hi Hj Hki Hkj. rewrite swap_get by assumption.
  replace (k =? j) with false by (symmetry; apply eqb_false_spec; apply phi_neq; exact Hkj).
  replace (k =? i) with false by (symmetry; apply eqb_false_spec; apply phi_neq; exact Hki).
  reflexivity.
Qed.

Lemma part_loop_spec : forall (a0 : array int) (p hi1 lo : int),
  ((φ hi1) < (φ (PArray.length a0)))%Z -> a0.[hi1] = p ->
  forall (z : Z) (i j : int) (a : array int) (H : Acc (Zwf 0) (gap hi1 j)) b i',
  gap hi1 j = z ->
  ((φ lo) <= (φ i) <= (φ j))%Z -> ((φ j) <= (φ hi1))%Z ->
  sim lo hi1 a0 a ->
  (forall k, ((φ lo) <= (φ k) < (φ i))%Z -> ((φ (a.[k])) < (φ p))%Z) ->
  (forall k, ((φ i) <= (φ k) < (φ j))%Z -> ((φ p) <= (φ (a.[k])))%Z) ->
  part_loop a p hi1 i j H = (b, i') ->
  ((φ lo) <= (φ i') <= (φ hi1))%Z /\ sim lo hi1 a0 b /\
  (forall k, ((φ lo) <= (φ k) < (φ i'))%Z -> ((φ (b.[k])) < (φ p))%Z) /\
  (forall k, ((φ i') <= (φ k) < (φ hi1))%Z -> ((φ p) <= (φ (b.[k])))%Z).
Proof.
  intros a0 p hi1 lo Hhi1 Hp z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i j a H b i' Hz Hij Hjh Hsim Hlt Hge Hrun.
  rewrite part_loop_eq in Hrun.
  pose proof Hsim as [HL _].
  destruct (bdec (j <? hi1)) as [Hj | Hj].
  - pose proof Hj as Hj'. rewrite ltb_spec in Hj'.
    assert (Hj1 : (φ (j + 1)) = ((φ j) + 1)%Z) by sia.
    destruct (a.[j] <? p) eqn:Ec.
    + rewrite ltb_spec in Ec.
      assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
      assert (Hlen : (φ (PArray.length a)) = (φ (PArray.length a0))) by (rewrite HL; reflexivity).
      eapply IH; [ | reflexivity | | | | | | exact Hrun].
      * rewrite <- Hz. apply dec_step. exact Hj.
      * lia.
      * lia.
      * eapply sim_trans; [exact Hsim|]. apply sim_swap; lia.
      * intros k Hk. destruct (Z.eq_dec (φ k) (φ i)) as [E|E].
        -- assert (k = i) by (apply to_Z_inj; exact E). subst k.
           rewrite swap_get_i by lia. exact Ec.
        -- rewrite swap_get_other by lia. apply Hlt. lia.
      * intros k Hk. destruct (Z.eq_dec (φ k) (φ j)) as [E|E].
        -- assert (k = j) by (apply to_Z_inj; exact E). subst k.
           rewrite swap_get_j by lia. apply Hge. lia.
        -- rewrite swap_get_other by lia. apply Hge. lia.
    + rewrite <- Bool.not_true_iff_false, ltb_spec in Ec.
      eapply IH; [ | reflexivity | | | exact Hsim | exact Hlt | | exact Hrun].
      * rewrite <- Hz. apply dec_step. exact Hj.
      * lia.
      * lia.
      * intros k Hk. destruct (Z.eq_dec (φ k) (φ j)) as [E|E].
        -- assert (k = j) by (apply to_Z_inj; exact E). subst k. lia.
        -- apply Hge. lia.
  - injection Hrun as <- <-.
    rewrite <- Bool.not_true_iff_false, ltb_spec in Hj.
    split; [lia|]. split; [exact Hsim|]. split; [exact Hlt|].
    intros k Hk. apply Hge. lia.
Qed.

Lemma partition_spec : forall (a : array int) (lo hi : int) b m,
  ((φ lo) + 1 < (φ hi))%Z -> ((φ hi) <= (φ (PArray.length a)))%Z ->
  partition a lo hi = (b, m) ->
  ((φ lo) <= (φ m) < (φ hi))%Z /\ sim lo hi a b /\
  (forall k, ((φ lo) <= (φ k) < (φ m))%Z -> ((φ (b.[k])) < (φ (b.[m])))%Z) /\
  (forall k, ((φ m) < (φ k) < (φ hi))%Z -> ((φ (b.[m])) <= (φ (b.[k])))%Z).
Proof.
  intros a lo hi b m Hlh Hha Hrun. unfold partition in Hrun.
  pose proof (to_Z_bounded lo) as Blo.
  assert (Hmid : ((φ lo) <= (φ (lo + (hi - lo) / 2)) < (φ hi))%Z) by sia.
  assert (Hhi1 : (φ (hi - 1)) = ((φ hi) - 1)%Z) by sia.
  set (mid := lo + (hi - lo) / 2) in *.
  set (a1 := swap a mid (hi - 1)) in *.
  assert (S1 : sim lo hi a a1) by (apply sim_swap; lia).
  assert (L1 : PArray.length a1 = PArray.length a) by apply swap_length.
  destruct (part_loop a1 a1.[hi - 1] (hi - 1) lo lo
              (Zwf_well_founded 0 (gap (hi - 1) lo))) as [a2 i] eqn:E2.
  injection Hrun as <- <-.
  destruct (part_loop_spec a1 a1.[hi - 1] (hi - 1) lo
              ltac:(rewrite L1; lia) eq_refl _ lo lo a1 _ a2 i eq_refl
              ltac:(lia) ltac:(lia) (sim_refl _ _ _)
              ltac:(intros k Hk; lia) ltac:(intros k Hk; lia) E2)
    as [Hi [S2 [Hlt Hge]]].
  pose proof S2 as [L2 [O2 _]].
  assert (Hp : a2.[hi - 1] = a1.[hi - 1]) by (apply O2; lia).
  assert (La2 : (φ (PArray.length a2)) = (φ (PArray.length a))) by (rewrite L2, L1; reflexivity).
  split; [lia|]. split.
  - eapply sim_trans; [exact S1|]. eapply sim_trans.
    + apply (sim_widen lo (hi - 1)); [lia | lia | exact S2].
    + apply sim_swap; lia.
  - rewrite swap_get_i by lia. rewrite Hp. split.
    + intros k Hk. rewrite swap_get_other by lia. apply Hlt. lia.
    + intros k Hk. destruct (Z.eq_dec (φ k) (φ (hi - 1))) as [E|E].
      * assert (k = hi - 1) by (apply to_Z_inj; exact E). subst k.
        rewrite swap_get_j by lia. apply Hge. lia.
      * rewrite swap_get_other by lia. apply Hge. lia.
Qed.

Definition sorted_on (lo hi : int) (b : array int) : Prop :=
  forall k1 k2, ((φ lo) <= (φ k1))%Z -> ((φ k1) < (φ k2))%Z -> ((φ k2) < (φ hi))%Z ->
    ((φ (b.[k1])) <= (φ (b.[k2])))%Z.

Lemma qsort_spec : forall (z : Z) (lo hi : int) (a : array int) (H : Acc (Zwf 0) (gap hi lo)),
  gap hi lo = z -> ((φ lo) <= (φ hi))%Z -> ((φ hi) <= (φ (PArray.length a)))%Z ->
  sim lo hi a (qsort a lo hi H) /\ sorted_on lo hi (qsort a lo hi H).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros lo hi a H Hz Hlh Hha.
  pose proof (alength_bound a) as Ba.
  rewrite qsort_eq.
  destruct (bdec (lo + 1 <? hi)) as [Hc | Hc].
  - assert (Hc' : ((φ lo) + 1 < (φ hi))%Z) by (rewrite ltb_spec in Hc; sia).
    destruct (partition a lo hi) as [a1 m] eqn:Ep.
    destruct (partition_spec a lo hi a1 m Hc' Hha Ep) as [Hm [S1 [Plt Pge]]].
    destruct (bdec ((lo <=? m) && (m <? hi))) as [Hb | Hb].
    2:{ exfalso. assert (E1 : (lo <=? m) = true) by (apply leb_spec; lia).
        assert (E2 : (m <? hi) = true) by (apply ltb_spec; lia).
        rewrite E1, E2 in Hb. discriminate. }
    pose proof S1 as [L1 _].
    assert (Hm1 : (φ (m + 1)) = ((φ m) + 1)%Z) by sia.
    set (H1 := Acc_inv H (dec_left lo hi m Hb)).
    set (a2 := qsort a1 lo m H1).
    destruct (IH (gap m lo) ltac:(rewrite <- Hz; apply dec_left; exact Hb)
                lo m a1 H1 eq_refl ltac:(lia) ltac:(rewrite L1; lia)) as [S2 T2].
    fold a2 in S2, T2.
    pose proof S2 as [L2 [O2 [G2 _]]].
    set (H2 := Acc_inv H (dec_right lo hi m Hb)).
    destruct (IH (gap hi (m + 1)) ltac:(rewrite <- Hz; apply dec_right; exact Hb)
                (m + 1) hi a2 H2 eq_refl ltac:(lia) ltac:(rewrite L2, L1; lia)) as [S3 T3].
    pose proof S3 as [L3 [O3 [G3 _]]].
    set (a3 := qsort a2 (m + 1) hi H2) in *.
    split.
    + eapply sim_trans; [exact S1|]. eapply sim_trans.
      * apply (sim_widen lo m); [lia|lia|exact S2].
      * apply (sim_widen (m + 1) hi); [lia|lia|exact S3].
    + (* every cell of [lo, m] is <= the pivot, every cell of (m, hi) is >= *)
      assert (Left : forall k, ((φ lo) <= (φ k) <= (φ m))%Z -> ((φ (a3.[k])) <= (φ (a1.[m])))%Z).
      { intros k Hk. rewrite O3 by lia.
        destruct (Z.eq_dec (φ k) (φ m)) as [E|E].
        - assert (k = m) by (apply to_Z_inj; exact E). subst k.
          rewrite O2 by lia. lia.
        - destruct (G2 k ltac:(lia)) as [k' [Hk' E']]. rewrite E'.
          pose proof (Plt k' Hk'). lia. }
      assert (Right : forall k, ((φ m) < (φ k) < (φ hi))%Z -> ((φ (a1.[m])) <= (φ (a3.[k])))%Z).
      { intros k Hk. destruct (G3 k ltac:(lia)) as [k' [Hk' E']]. rewrite E'.
        rewrite O2 by lia. apply Pge. lia. }
      intros k1 k2 H1' H12 H2'.
      destruct (Z_lt_le_dec (φ k2) (φ m)) as [C2|C2].
      * rewrite !O3 by lia. apply T2; lia.
      * destruct (Z_lt_le_dec (φ m) (φ k1)) as [C1|C1].
        -- apply T3; lia.
        -- destruct (Z.eq_dec (φ k2) (φ m)) as [E|E].
           ++ assert (k2 = m) by (apply to_Z_inj; exact E). subst k2.
              rewrite (O3 m) by lia. rewrite (O2 m) by lia. apply Left. lia.
           ++ pose proof (Left k1 ltac:(lia)). pose proof (Right k2 ltac:(lia)). lia.
  - assert (Hc' : ((φ hi) <= (φ lo) + 1)%Z) by (rewrite <- Bool.not_true_iff_false, ltb_spec in Hc; sia).
    split; [apply sim_refl|].
    intros k1 k2 H1 H12 H2. lia.
Qed.

Lemma sort_all_spec : forall a,
  sim 0 (PArray.length a) a (sort_all a) /\ sorted_on 0 (PArray.length a) (sort_all a).
Proof.
  intros a. unfold sort_all. apply (qsort_spec _ 0 (PArray.length a) a _ eq_refl).
  - pose proof (to_Z_bounded (PArray.length a)). change (φ 0) with 0%Z. lia.
  - lia.
Qed.

Lemma sweep_eq : forall A R n p q best H,
  sweep A R n p q best H =
  match bdec (p <? n) with
  | left Hp =>
      match bdec ((q <? n) && (R.[q] <=? A.[p])) with
      | left Hq => sweep A R n p (q + 1) best (Acc_inv H (dec_q A R n p q Hp Hq))
      | right _ =>
          sweep A R n (p + 1) q (if best + q <? p + 1 then p + 1 - q else best)
            (Acc_inv H (dec_p n p q Hp))
      end
  | right _ => best
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition cnt_le (t : Z) (l : list Z) : nat := List.length (filter (fun x => (x <=? t)%Z) l).

Lemma filter_all_true : forall {A} (f : A -> bool) l,
  (forall x, In x l -> f x = true) -> List.length (filter f l) = List.length l.
Proof.
  intros A f l H. induction l as [| x l IH]; simpl; [reflexivity|].
  rewrite (H x (or_introl eq_refl)). simpl. rewrite IH; [reflexivity|].
  intros y Hy. apply H. right. exact Hy.
Qed.

Lemma filter_all_false : forall {A} (f : A -> bool) l,
  (forall x, In x l -> f x = false) -> List.length (filter f l) = 0%nat.
Proof.
  intros A f l H. induction l as [| x l IH]; simpl; [reflexivity|].
  rewrite (H x (or_introl eq_refl)). apply IH.
  intros y Hy. apply H. right. exact Hy.
Qed.

Lemma cnt_split : forall (g : nat -> Z) (t : Z) (n q : nat), (q <= n)%nat ->
  (forall k, (k < q)%nat -> (g k <= t)%Z) ->
  (forall k, (q <= k < n)%nat -> (t < g k)%Z) ->
  cnt_le t (map g (seq 0 n)) = q.
Proof.
  intros g t n q Hqn H1 H2. unfold cnt_le.
  replace n with (q + (n - q))%nat by lia.
  rewrite seq_app, map_app, filter_app, length_app.
  rewrite filter_all_true, filter_all_false.
  - rewrite length_map, length_seq. lia.
  - intros x Hx. apply in_map_iff in Hx. destruct Hx as [k [<- Hk]]. apply in_seq in Hk.
    apply Z.leb_gt. apply H2. lia.
  - intros x Hx. apply in_map_iff in Hx. destruct Hx as [k [<- Hk]]. apply in_seq in Hk.
    apply Z.leb_le. apply H1. lia.
Qed.

Lemma cnt_view : forall (R : array int) (t : Z) (q : int),
  ((φ q) <= (φ (PArray.length R)))%Z ->
  (forall m, ((φ m) < (φ q))%Z -> ((φ (R.[m])) <= t)%Z) ->
  (forall m, ((φ q) <= (φ m) < (φ (PArray.length R)))%Z -> (t < (φ (R.[m])))%Z) ->
  cnt_le t (view R) = Z.to_nat (φ q).
Proof.
  intros R t q Hq H1 H2. unfold view. pose proof (alength_bound R).
  apply cnt_split.
  - lia.
  - intros k Hk. apply H1. rewrite phi_of_nat by (rewrite wB_val; lia). lia.
  - intros k Hk. apply H2. rewrite phi_of_nat by (rewrite wB_val; lia). lia.
Qed.

Definition sweep_val (A R : array int) (p : int) : Z :=
  ((φ p) + 1 - Z.of_nat (cnt_le (φ (A.[p])) (view R)))%Z.

Lemma sweep_spec : forall (A R : array int) (n : int),
  PArray.length A = n -> PArray.length R = n ->
  sorted_on 0 n A -> sorted_on 0 n R ->
  forall (z : Z) (p q best : int) (H : Acc (Zwf 0) (meas n p q)),
  meas n p q = z ->
  ((φ p) <= (φ n))%Z -> ((φ q) <= (φ n))%Z -> (0 <= (φ best) <= (φ p))%Z ->
  (((φ p) < (φ n))%Z -> forall m, ((φ m) < (φ q))%Z -> ((φ (R.[m])) <= (φ (A.[p])))%Z) ->
  ((φ best) = 0%Z \/ exists p', ((φ p') < (φ p))%Z /\ (φ best) = sweep_val A R p') ->
  (forall p', ((φ p') < (φ p))%Z -> (sweep_val A R p' <= (φ best))%Z) ->
  let r := sweep A R n p q best H in
  ((φ r) = 0%Z \/ exists p', ((φ p') < (φ n))%Z /\ (φ r) = sweep_val A R p') /\
  (forall p', ((φ p') < (φ n))%Z -> (sweep_val A R p' <= (φ r))%Z).
Proof.
  intros A R n LA LR SA SR z.
  pose proof (alength_bound A) as BA. rewrite LA in BA.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros p q best H Hz Hp Hq Hb Hpref Hex Hmax r. unfold r; clear r.
  rewrite sweep_eq.
  destruct (bdec (p <? n)) as [Hpn | Hpn].
  - pose proof Hpn as Hpn'. rewrite ltb_spec in Hpn'.
    destruct (bdec ((q <? n) && (R.[q] <=? A.[p]))) as [Hc | Hc].
    + pose proof Hc as Hc'. apply andb_prop in Hc'. destruct Hc' as [Hqn HRA].
      rewrite ltb_spec in Hqn. rewrite leb_spec in HRA.
      assert (E : (φ (q + 1)) = ((φ q) + 1)%Z) by sia.
      apply (IH (meas n p (q + 1))); [rewrite <- Hz; exact (dec_q A R n p q Hpn Hc)
            | reflexivity | lia | lia | lia | | exact Hex | exact Hmax].
      intros _ m Hm. destruct (Z.eq_dec (φ m) (φ q)) as [Em|Em].
      * assert (m = q) by (apply to_Z_inj; exact Em). subst m. exact HRA.
      * apply Hpref; [exact Hpn'| lia].
    + assert (Hcnt : cnt_le (φ (A.[p])) (view R) = Z.to_nat (φ q)).
      { apply cnt_view; [rewrite LR; exact Hq | exact (Hpref Hpn') |].
        intros m Hm. rewrite LR in Hm.
        assert (Hqn : ((φ q) < (φ n))%Z) by lia.
        assert (HRA : ((φ (A.[p])) < (φ (R.[q])))%Z).
        { destruct (Z_lt_le_dec (φ (A.[p])) (φ (R.[q]))) as [C|C]; [exact C|].
          exfalso. assert (E1 : (q <? n) = true) by (apply ltb_spec; exact Hqn).
          assert (E2 : (R.[q] <=? A.[p]) = true) by (apply leb_spec; exact C).
          rewrite E1, E2 in Hc. discriminate. }
        destruct (Z.eq_dec (φ m) (φ q)) as [Em|Em].
        - assert (m = q) by (apply to_Z_inj; exact Em). subst m. exact HRA.
        - pose proof (SR q m ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
      assert (Hsv : sweep_val A R p = ((φ p) + 1 - (φ q))%Z)
        by (unfold sweep_val; rewrite Hcnt; lia).
      assert (E : (φ (p + 1)) = ((φ p) + 1)%Z) by sia.
      set (best' := if best + q <? p + 1 then p + 1 - q else best).
      assert (Hb' : (φ best') = Z.max (φ best) ((φ p) + 1 - (φ q))).
      { unfold best'. destruct (best + q <? p + 1) eqn:Eb.
        - rewrite ltb_spec in Eb. assert ((φ (best + q)) = ((φ best) + (φ q))%Z) by sia.
          assert ((φ (p + 1 - q)) = ((φ p) + 1 - (φ q))%Z) by sia. lia.
        - rewrite <- Bool.not_true_iff_false, ltb_spec in Eb.
          assert ((φ (best + q)) = ((φ best) + (φ q))%Z) by sia. lia. }
      apply (IH (meas n (p + 1) q)); [rewrite <- Hz; exact (dec_p n p q Hpn)
            | reflexivity | lia | lia | lia | | | ].
      * intros Hp1 m Hm. pose proof (Hpref Hpn' m Hm).
        pose proof (SA p (p + 1) ltac:(change (φ 0) with 0%Z; pose proof (to_Z_bounded p); lia)
                      ltac:(lia) ltac:(lia)). lia.
      * destruct (Z.max_spec (φ best) ((φ p) + 1 - (φ q))) as [[_ M]|[_ M]]; rewrite Hb', M.
        -- right. exists p. split; [lia|]. rewrite Hsv. reflexivity.
        -- destruct Hex as [Hex|[p' [Hp' Hex]]]; [left; exact Hex|].
           right. exists p'. split; [lia|exact Hex].
      * intros p' Hp'. rewrite Hb'. destruct (Z.eq_dec (φ p') (φ p)) as [Ep|Ep].
        -- assert (p' = p) by (apply to_Z_inj; exact Ep). subst p'. lia.
        -- pose proof (Hmax p' ltac:(lia)). lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hpn.
    split.
    + destruct Hex as [Hex|[p' [Hp' Hex]]]; [left; exact Hex|].
      right. exists p'. split; [lia|exact Hex].
    + intros p' Hp'. apply Hmax. lia.
Qed.

(* The same closed form over Z. *)
Definition leapZ (y : Z) : bool :=
  ((y mod 4 =? 0) && negb (y mod 100 =? 0) || (y mod 400 =? 0))%Z.

Definition cby (y : Z) : Z := (365 * y + (y + 3) / 4 - (y + 99) / 100 + (y + 399) / 400)%Z.

Definition cbm (y m : Z) : Z :=
  ((367 * m - 362) / 12 - (if m <=? 2 then 0 else if leapZ y then 1 else 2))%Z.

Lemma dby_ok : forall y : N, (2013 <= y <= 2016)%N ->
  Z.of_N (sum_below days_in_year (N.to_nat y)) = cby (Z.of_N y).
Proof.
  intros y Hy.
  assert (y = 2013 \/ y = 2014 \/ y = 2015 \/ y = 2016)%N as Hc by lia.
  destruct Hc as [ -> | [ -> | [ -> | -> ]]]; vm_compute; reflexivity.
Qed.

Lemma dbm_ok : forall y m : N, (2013 <= y <= 2016)%N -> (1 <= m <= 12)%N ->
  Z.of_N (sum_below (fun k => days_in_month y (k + 1)) (N.to_nat (m - 1)))
  = cbm (Z.of_N y) (Z.of_N m).
Proof.
  intros y m Hy Hm.
  assert (y = 2013 \/ y = 2014 \/ y = 2015 \/ y = 2016)%N as Hc by lia.
  assert (m = 1 \/ m = 2 \/ m = 3 \/ m = 4 \/ m = 5 \/ m = 6 \/ m = 7 \/ m = 8 \/
          m = 9 \/ m = 10 \/ m = 11 \/ m = 12)%N as Hd by lia.
  destruct Hc as [ -> | [ -> | [ -> | -> ]]];
  destruct Hd as [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | -> ]]]]]]]]]]];
  vm_compute; reflexivity.
Qed.

Definition zmin (t : datetime N) : Z :=
  (((cby (Z.of_N (year t)) + cbm (Z.of_N (year t)) (Z.of_N (month t))
     + (Z.of_N (day t) - 1)) * 24 + Z.of_N (hour t)) * 60 + Z.of_N (minute t))%Z.

Lemma minutes_closed : forall t, valid_datetime t -> Z.of_N (minutes t) = zmin t.
Proof.
  intros t [Hy [Hm [Hd [Hh Hmi]]]].
  unfold minutes, zmin. cbv zeta.
  pose proof (dby_ok (year t) Hy) as E1.
  pose proof (dbm_ok (year t) (month t) Hy Hm) as E2.
  rewrite N2Z.inj_add, N2Z.inj_mul, N2Z.inj_add, N2Z.inj_mul, !N2Z.inj_add, E1, E2.
  rewrite N2Z.inj_sub by lia. reflexivity.
Qed.

Lemma add_small : forall a b : int, ((φ a) + (φ b) < wB)%Z -> (φ (a + b)) = ((φ a) + (φ b))%Z.
Proof.
  intros a b H. rewrite add_spec. apply Z.mod_small.
  pose proof (to_Z_bounded a). pose proof (to_Z_bounded b). lia.
Qed.

Lemma sub_small : forall a b : int, ((φ b) <= (φ a))%Z -> (φ (a - b)) = ((φ a) - (φ b))%Z.
Proof.
  intros a b H. rewrite sub_spec. apply Z.mod_small.
  pose proof (to_Z_bounded a). pose proof (to_Z_bounded b). lia.
Qed.

Lemma mul_small : forall a b : int, ((φ a) * (φ b) < wB)%Z -> (φ (a * b)) = ((φ a) * (φ b))%Z.
Proof.
  intros a b H. rewrite mul_spec. apply Z.mod_small.
  pose proof (to_Z_bounded a). pose proof (to_Z_bounded b). nia.
Qed.

Lemma eqb_Z : forall a b : int, (a =? b) = ((φ a) =? (φ b))%Z.
Proof.
  intros a b. destruct (a =? b) eqn:E; symmetry.
  - apply eqb_spec in E. subst. apply Z.eqb_refl.
  - apply Z.eqb_neq. intro F. apply eqb_false_spec in E. apply E. apply to_Z_inj. exact F.
Qed.

Lemma leb_Z : forall a b : int, (a <=? b) = ((φ a) <=? (φ b))%Z.
Proof.
  intros a b. destruct (a <=? b) eqn:E; symmetry.
  - apply leb_spec in E. apply Z.leb_le. exact E.
  - apply Z.leb_gt. rewrite <- Bool.not_true_iff_false, leb_spec in E. lia.
Qed.

Lemma ltb_Z : forall a b : int, (a <? b) = ((φ a) <? (φ b))%Z.
Proof.
  intros a b. destruct (a <? b) eqn:E; symmetry.
  - apply ltb_spec in E. apply Z.ltb_lt. exact E.
  - apply Z.ltb_ge. rewrite <- Bool.not_true_iff_false, ltb_spec in E. lia.
Qed.

Lemma leapb_ok : forall y, leapb y = leapZ (φ y).
Proof.
  intros y. unfold leapb, leapZ. rewrite !eqb_Z, !mod_spec. reflexivity.
Qed.

Lemma dby_mach : forall y, ((φ y) <= 10000)%Z -> (φ (days_before_year y)) = cby (φ y).
Proof.
  intros y Hy. unfold days_before_year, cby. pose proof (to_Z_bounded y) as By.
  assert (A1 : (φ (365 * y)) = (365 * (φ y))%Z) by sia.
  assert (A2 : (φ ((y + 3) / 4)) = (((φ y) + 3) / 4)%Z)
    by (rewrite div_spec; f_equal; sia).
  assert (A3 : (φ ((y + 99) / 100)) = (((φ y) + 99) / 100)%Z)
    by (rewrite div_spec; f_equal; sia).
  assert (A4 : (φ ((y + 399) / 400)) = (((φ y) + 399) / 400)%Z)
    by (rewrite div_spec; f_equal; sia).
  assert (Q1 : (0 <= ((φ y) + 3) / 4 <= (φ y) + 3)%Z)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (Q2 : (0 <= ((φ y) + 99) / 100 <= (φ y) + 99)%Z)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (Q3 : (0 <= ((φ y) + 399) / 400 <= (φ y) + 399)%Z)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (Q21 : (((φ y) + 99) / 100 <= ((φ y) + 3) / 4 + 365 * (φ y))%Z).
  { assert ((((φ y) + 99) / 100 <= ((φ y) + 99) / 4)%Z)
      by (apply Z.div_le_compat_l; lia).
    assert ((((φ y) + 99) / 4 <= ((φ y) + 3) / 4 + 24)%Z).
    { replace ((φ y) + 99)%Z with ((φ y) + 3 + 24 * 4)%Z by lia.
      rewrite Z.div_add by lia. lia. }
    destruct (Z.eq_dec (φ y) 0) as [E|E].
    - rewrite E. cbn. lia.
    - lia. }
  set (m1 := 365 * y) in *. set (m2 := (y + 3) / 4) in *.
  set (m3 := (y + 99) / 100) in *. set (m4 := (y + 399) / 400) in *.
  set (q1 := (((φ y) + 3) / 4)%Z) in *. set (q2 := (((φ y) + 99) / 100)%Z) in *.
  set (q3 := (((φ y) + 399) / 400)%Z) in *.
  rewrite add_spec, sub_spec, add_spec, A1, A2, A3, A4.
  rewrite (Z.mod_small (365 * (φ y) + q1)) by lia.
  rewrite (Z.mod_small (365 * (φ y) + q1 - q2)) by lia.
  apply Z.mod_small. lia.
Qed.

Lemma dbm_mach : forall y m, (1 <= (φ m) <= 12)%Z ->
  (φ (days_before_month y m)) = cbm (φ y) (φ m).
Proof.
  intros y m Hm. unfold days_before_month, cbm.
  rewrite leb_Z, leapb_ok. change (φ 2) with 2%Z.
  assert (A : (φ ((367 * m - 362) / 12)) = ((367 * (φ m) - 362) / 12)%Z)
    by (rewrite div_spec; f_equal; sia).
  assert (Q : (30 * ((φ m) - 1) <= (367 * (φ m) - 362) / 12 <= 31 * ((φ m) - 1))%Z) by sia.
  set (w := (367 * m - 362) / 12) in *. set (q := ((367 * (φ m) - 362) / 12)%Z) in *.
  destruct ((φ m) <=? 2)%Z eqn:E; [|destruct (leapZ (φ y))];
  [rewrite Z.leb_le in E | rewrite Z.leb_gt in E..];
  rewrite sub_spec, A; [change (φ 0) with 0%Z | change (φ 1) with 1%Z | change (φ 2) with 2%Z];
  apply Z.mod_small; lia.
Qed.

Lemma cby_range : forall y, (2013 <= y <= 2016)%Z -> (0 <= cby y <= 740000)%Z.
Proof. intros y Hy. unfold cby. sia. Qed.

Lemma cbm_range : forall y m, (1 <= m <= 12)%Z -> (0 <= cbm y m <= 340)%Z.
Proof.
  intros y m Hm. unfold cbm. destruct (m <=? 2)%Z eqn:E; [|destruct (leapZ y)];
  [rewrite Z.leb_le in E | rewrite Z.leb_gt in E..]; sia.
Qed.

Lemma zmin_range : forall t, valid_datetime t -> (0 <= zmin t <= 1100000000)%Z.
Proof.
  intros t Hv. pose proof Hv as [Hy [Hm [Hd [Hh Hmi]]]].
  assert (Hdm : (days_in_month (year t) (month t) <= 31)%N)
    by (unfold days_in_month; destruct (month t =? 2)%N; [destruct (leap (year t))|
        destruct (_ || _)]; lia).
  pose proof (cby_range (Z.of_N (year t)) ltac:(lia)).
  pose proof (cbm_range (Z.of_N (year t)) (Z.of_N (month t)) ltac:(lia)).
  unfold zmin. lia.
Qed.

Lemma mach_minutes_ok : forall (x : datetime uint) (t : datetime N),
  repr x t -> valid_datetime t -> (φ (mach_minutes x)) = zmin t.
Proof.
  intros x t Hr Hv. pose proof Hv as [Hy [Hm [Hd [Hh Hmi]]]].
  destruct Hr as [Ry [Rm [Rd [Rh Rmi]]]].
  unfold repr, repr_uint in Ry, Rm, Rd, Rh, Rmi.
  assert (Hdm : (days_in_month (year t) (month t) <= 31)%N)
    by (unfold days_in_month; destruct (month t =? 2)%N; [destruct (leap (year t))|
        destruct (_ || _)]; lia).
  pose proof (to_Z_bounded (year x)). pose proof (to_Z_bounded (month x)).
  pose proof (to_Z_bounded (day x)). pose proof (to_Z_bounded (hour x)).
  pose proof (to_Z_bounded (minute x)).
  assert (Y : (φ (year x)) = Z.of_N (year t)) by lia.
  assert (M : (φ (month x)) = Z.of_N (month t)) by lia.
  assert (D : (φ (day x)) = Z.of_N (day t)) by lia.
  assert (Ho : (φ (hour x)) = Z.of_N (hour t)) by lia.
  assert (Mi : (φ (minute x)) = Z.of_N (minute t)) by lia.
  unfold mach_minutes, zmin. cbv zeta.
  pose proof (dby_mach (year x) ltac:(lia)) as E1.
  pose proof (dbm_mach (year x) (month x) ltac:(lia)) as E2.
  pose proof (cby_range (Z.of_N (year t)) ltac:(lia)).
  pose proof (cbm_range (Z.of_N (year t)) (Z.of_N (month t)) ltac:(lia)).
  rewrite Y in E1, E2. rewrite M in E2.
  set (u := days_before_year (year x)) in *.
  set (v := days_before_month (year x) (month x)) in *.
  set (cy := cby (Z.of_N (year t))) in *.
  set (cm := cbm (Z.of_N (year t)) (Z.of_N (month t))) in *.
  pose proof wB_val as WB.
  assert (S1 : (φ (u + v)) = (cy + cm)%Z) by (rewrite add_small; lia).
  assert (S2 : (φ (day x - 1)) = (Z.of_N (day t) - 1)%Z)
    by (rewrite sub_small; change (φ 1) with 1%Z; lia).
  assert (S3 : (φ (u + v + (day x - 1))) = (cy + cm + (Z.of_N (day t) - 1))%Z)
    by (rewrite add_small; rewrite ?S1, ?S2; lia).
  assert (S4 : (φ ((u + v + (day x - 1)) * 24)) = ((cy + cm + (Z.of_N (day t) - 1)) * 24)%Z)
    by (rewrite mul_small; rewrite S3; change (φ 24) with 24%Z; lia).
  assert (S5 : (φ ((u + v + (day x - 1)) * 24 + hour x))
               = ((cy + cm + (Z.of_N (day t) - 1)) * 24 + Z.of_N (hour t))%Z)
    by (rewrite add_small; rewrite S4; lia).
  assert (S6 : (φ (((u + v + (day x - 1)) * 24 + hour x) * 60))
               = (((cy + cm + (Z.of_N (day t) - 1)) * 24 + Z.of_N (hour t)) * 60)%Z)
    by (rewrite mul_small; rewrite S5; change (φ 60) with 60%Z; lia).
  rewrite add_small; rewrite S6; lia.
Qed.

Definition zal (a r i : Z) : Z :=
  if (a =? r)%Z then (a * 20000 + 5000 + 2 * i)%Z else (a * 20000 + 15000 + i)%Z.

Definition zrh (a r i : Z) : Z :=
  if (a =? r)%Z then (a * 20000 + 5001 + 2 * i)%Z else (r * 20000 + i)%Z.

Lemma key_al_ok : forall ma r i : int,
  ((φ ma) <= 2000000000)%Z -> ((φ r) <= 2000000000)%Z -> ((φ i) < 5000)%Z ->
  (φ (key_al ma r i)) = zal (φ ma) (φ r) (φ i).
Proof.
  intros ma r i Ha Hr Hi. unfold key_al, zal. rewrite eqb_Z.
  destruct ((φ ma) =? (φ r))%Z; sia.
Qed.

Lemma key_rh_ok : forall ma r i : int,
  ((φ ma) <= 2000000000)%Z -> ((φ r) <= 2000000000)%Z -> ((φ i) < 5000)%Z ->
  (φ (key_rh ma r i)) = zrh (φ ma) (φ r) (φ i).
Proof.
  intros ma r i Ha Hr Hi. unfold key_rh, zrh. rewrite eqb_Z.
  destruct ((φ ma) =? (φ r))%Z; sia.
Qed.

Lemma key_conflict : forall ai ri aj rj i j : Z,
  (0 <= ai <= ri)%Z -> (0 <= aj <= rj)%Z -> (0 <= i < 5000)%Z -> (0 <= j < 5000)%Z -> i <> j ->
  ((zal aj rj j < zrh ai ri i /\ zal ai ri i < zrh aj rj j)%Z <-> ~ (ri <= aj \/ rj <= ai)%Z).
Proof.
  intros ai ri aj rj i j Hi Hj Hi' Hj' Hne. unfold zal, zrh.
  destruct (Z.eqb_spec ai ri), (Z.eqb_spec aj rj); lia.
Qed.

Lemma key_nonempty : forall a r i : Z, (0 <= a <= r)%Z -> (0 <= i < 5000)%Z ->
  (zal a r i < zrh a r i)%Z.
Proof. intros a r i Ha Hi. unfold zal, zrh. destruct (Z.eqb_spec a r); lia. Qed.

Lemma key_inj : forall ai ri aj rj i j : Z,
  (0 <= ai <= ri)%Z -> (0 <= aj <= rj)%Z -> (0 <= i < 5000)%Z -> (0 <= j < 5000)%Z ->
  zal ai ri i = zal aj rj j -> i = j.
Proof.
  intros ai ri aj rj i j Hi Hj Hi' Hj'. unfold zal.
  destruct (Z.eqb_spec ai ri), (Z.eqb_spec aj rj); lia.
Qed.

Lemma fill_eq : forall xa xd c n k A R H,
  fill xa xd c n k A R H =
  match bdec (k <? n) with
  | left Hk =>
      let ma := mach_minutes xa.[k] in
      let r := mach_minutes xd.[k] + c in
      fill xa xd c n (k + 1) A.[k <- key_al ma r k] R.[k <- key_rh ma r k]
        (Acc_inv H (dec_step n k Hk))
  | right _ => (A, R)
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Proof of the program                                                *)
(* ------------------------------------------------------------------ *)

Lemma fill_spec : forall (xa xd : array (datetime uint)) (c n : int) (fa fr : nat -> Z),
  (forall k, ((φ k) < (φ n))%Z ->
     (φ (key_al (mach_minutes xa.[k]) (mach_minutes xd.[k] + c) k)) = fa (Z.to_nat (φ k)) /\
     (φ (key_rh (mach_minutes xa.[k]) (mach_minutes xd.[k] + c) k)) = fr (Z.to_nat (φ k))) ->
  forall (z : Z) (k : int) (A R : array int) (H : Acc (Zwf 0) (gap n k)) A' R',
  gap n k = z -> ((φ k) <= (φ n))%Z -> PArray.length A = n -> PArray.length R = n ->
  (forall k', ((φ k') < (φ k))%Z ->
     (φ (A.[k'])) = fa (Z.to_nat (φ k')) /\ (φ (R.[k'])) = fr (Z.to_nat (φ k'))) ->
  fill xa xd c n k A R H = (A', R') ->
  PArray.length A' = n /\ PArray.length R' = n /\
  (forall k', ((φ k') < (φ n))%Z ->
     (φ (A'.[k'])) = fa (Z.to_nat (φ k')) /\ (φ (R'.[k'])) = fr (Z.to_nat (φ k'))).
Proof.
  intros xa xd c n fa fr Hcell z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k A R H A' R' Hz Hk LA LR Hinv Hrun.
  rewrite fill_eq in Hrun.
  destruct (bdec (k <? n)) as [Hkn | Hkn].
  - pose proof Hkn as Hkn'. rewrite ltb_spec in Hkn'.
    assert (E : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
    eapply IH; [ | reflexivity | | | | | exact Hrun].
    + rewrite <- Hz. apply dec_step. exact Hkn.
    + lia.
    + rewrite alength_set. exact LA.
    + rewrite alength_set. exact LR.
    + intros k' Hk'. destruct (Z.eq_dec (φ k') (φ k)) as [Ek|Ek].
      * assert (k' = k) by (apply to_Z_inj; exact Ek). subst k'.
        rewrite !aget_set_same by (rewrite ?LA, ?LR; exact Hkn).
        apply Hcell. exact Hkn'.
      * rewrite !aget_set_other by (apply phi_neq; lia). apply Hinv. lia.
  - injection Hrun as <- <-. rewrite <- Bool.not_true_iff_false, ltb_spec in Hkn.
    split; [exact LA|]. split; [exact LR|]. intros k' Hk'. apply Hinv. lia.
Qed.

Lemma view_eq : forall (A : array int) (f : nat -> Z) (nn : nat),
  (φ (PArray.length A)) = Z.of_nat nn ->
  (forall k', ((φ k') < (φ (PArray.length A)))%Z -> (φ (A.[k'])) = f (Z.to_nat (φ k'))) ->
  view A = map f (seq 0 nn).
Proof.
  intros A f nn HL Hc. unfold view. rewrite HL, Nat2Z.id. apply map_ext_in.
  intros k Hk. apply in_seq in Hk. pose proof (alength_bound A).
  assert (Hk' : (φ (of_Z (Z.of_nat k))) = Z.of_nat k) by (apply phi_of_nat; rewrite wB_val; lia).
  rewrite Hc by lia. rewrite Hk', Nat2Z.id. reflexivity.
Qed.

Lemma NoDup_map_eq : forall {A B} (f : A -> B) (l : list A) x y,
  NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  intros A B f l. induction l as [| a l IH]; intros x y Hn Hx Hy E; [destruct Hx|].
  simpl in Hn. inversion Hn as [| ? ? Hna Hnl]; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy].
  - reflexivity.
  - exfalso. apply Hna. rewrite E. apply in_map. exact Hy.
  - exfalso. apply Hna. rewrite <- E. apply in_map. exact Hx.
  - apply IH; assumption.
Qed.

Lemma cnt_le_map : forall (f : nat -> Z) t l,
  cnt_le t (map f l) = List.length (filter (fun j => (f j <=? t)%Z) l).
Proof.
  intros f t l. unfold cnt_le. induction l as [| x l IH]; simpl; [reflexivity|].
  destruct (f x <=? t)%Z; simpl; rewrite IH; reflexivity.
Qed.

Lemma cnt_le_perm : forall t l l', Permutation l l' -> cnt_le t l = cnt_le t l'.
Proof. intros t l l' P. unfold cnt_le. apply filter_length_perm. exact P. Qed.

Lemma sweep_val_cntD : forall (A' R' : array int) (n : int) (nn : nat) (al rh : nat -> Z),
  (φ n) = Z.of_nat nn -> PArray.length A' = n -> PArray.length R' = n ->
  Permutation (view A') (map al (seq 0 nn)) ->
  Permutation (view R') (map rh (seq 0 nn)) ->
  sorted_on 0 n A' ->
  NoDup (map al (seq 0 nn)) ->
  (forall j, In j (seq 0 nn) -> (al j < rh j)%Z) ->
  forall p, ((φ p) < (φ n))%Z ->
  sweep_val A' R' p = Z.of_nat (cntD al rh (φ (A'.[p])) (seq 0 nn)).
Proof.
  intros A' R' n nn al rh Hn LA LR PA PR SA ND Hne p Hp.
  set (t := (φ (A'.[p]))).
  pose proof (alength_bound A') as BA. rewrite LA in BA.
  pose proof (to_Z_bounded p) as Bp.
  assert (NDA : NoDup (view A')) by (apply (Permutation_NoDup (Permutation_sym PA)); exact ND).
  assert (Hcnt : cnt_le t (view A') = Z.to_nat (φ (p + 1))).
  { assert (E : (φ (p + 1)) = ((φ p) + 1)%Z) by sia.
    apply cnt_view; [rewrite LA; lia | |].
    - intros m Hm. rewrite E in Hm. destruct (Z.eq_dec (φ m) (φ p)) as [Em|Em].
      + assert (m = p) by (apply to_Z_inj; exact Em). subst m. unfold t. lia.
      + pose proof (to_Z_bounded m). apply SA; change (φ 0) with 0%Z; lia.
    - intros m Hm. rewrite LA in Hm. rewrite E in Hm.
      pose proof (SA p m ltac:(change (φ 0) with 0%Z; lia) ltac:(lia) ltac:(lia)) as Hle.
      assert (Hneq : (φ (A'.[p])) <> (φ (A'.[m]))).
      { intro Eq. unfold view in NDA. rewrite LA, Hn, Nat2Z.id in NDA.
        assert (Hpm : Z.to_nat (φ p) = Z.to_nat (φ m)).
        { apply (NoDup_map_eq _ _ _ _ NDA).
          - apply in_seq. lia.
          - apply in_seq. lia.
          - rewrite !Z2Nat.id by lia. rewrite !of_to_Z. exact Eq. }
        lia. }
      unfold t. lia. }
  rewrite (cnt_le_perm _ _ _ PA) in Hcnt.
  unfold sweep_val. fold t.
  rewrite (cnt_le_perm _ _ _ PR).
  rewrite cnt_le_map in Hcnt |- *.
  rewrite (filter_length_split (fun j => (al j <=? t)%Z) (fun j => (rh j <=? t)%Z)) in Hcnt.
  assert (E1 : List.length (filter (fun j => (al j <=? t)%Z && (rh j <=? t)%Z) (seq 0 nn))
             = List.length (filter (fun j => (rh j <=? t)%Z) (seq 0 nn))).
  { apply filter_length_ext. intros j Hj. pose proof (Hne j Hj).
    destruct (Z.leb_spec (rh j) t), (Z.leb_spec (al j) t); simpl; reflexivity || lia. }
  assert (E2 : List.length (filter (fun j => (al j <=? t)%Z && negb (rh j <=? t)%Z) (seq 0 nn))
             = cntD al rh t (seq 0 nn)).
  { unfold cntD. apply filter_length_ext. intros j _. unfold activeb.
    destruct (Z.leb_spec (rh j) t), (Z.ltb_spec t (rh j)); simpl;
      rewrite ?Bool.andb_true_r, ?Bool.andb_false_r; reflexivity || lia. }
  rewrite E1, E2 in Hcnt.
  assert (E : (φ (p + 1)) = ((φ p) + 1)%Z) by sia. rewrite E in Hcnt. lia.
Qed.

Definition d0 : datetime N :=
  {| year := 0%N; month := 0%N; day := 0%N; hour := 0%N; minute := 0%N |}.

Lemma repr_cell : forall (xa : array (datetime uint)) (arr : list (datetime N)),
  repr xa arr -> forall k : int, ((φ k) < Z.of_nat (List.length arr))%Z ->
  repr (xa.[k]) (nth (Z.to_nat (φ k)) arr d0).
Proof.
  intros xa arr [Hl Hc] k Hk.
  pose proof (to_Z_bounded k).
  destruct (Hc (Z.to_nat (φ k)) ltac:(lia)) as [m [Hm Hr]].
  rewrite (nth_error_nth _ _ _ Hm).
  rewrite Z2Nat.id in Hr by lia. rewrite of_to_Z in Hr. exact Hr.
Qed.

Lemma repr_len : forall (xa : array (datetime uint)) (arr : list (datetime N)),
  repr xa arr -> (φ (PArray.length xa)) = Z.of_nat (List.length arr).
Proof. intros xa arr [Hl _]. symmetry. exact Hl. Qed.

Lemma Forall2_nth_P : forall {A B} (P : A -> B -> Prop) l1 l2 d1 d2,
  Forall2 P l1 l2 -> forall i, (i < List.length l1)%nat -> P (nth i l1 d1) (nth i l2 d2).
Proof.
  intros A B P l1 l2 d1 d2 H. induction H as [| x y l1 l2 Hxy H IH]; intros i Hi.
  - simpl in Hi. lia.
  - destruct i; simpl; [exact Hxy|]. apply IH. simpl in Hi. lia.
Qed.

Lemma min_rooms_impl_correct :
  forall (c : N) (arr dep : list (datetime N)) (x : uint) (xa xd : array (datetime uint)),
  valid_input c arr dep -> repr x c -> repr xa arr -> repr xd dep ->
  exists k : N, repr (min_rooms_impl x xa xd) k /\ min_rooms_spec c arr dep k.
Proof.
  intros c arr dep x xa xd Hv Hx Ha Hd.
  destruct Hv as [Vb Vlen Vc Varr Vdep Vord].
  unfold len in Vb, Vlen.
  set (nn := List.length arr) in *.
  assert (Hdl : List.length dep = nn) by lia.
  pose proof (repr_len xa arr Ha) as LXa. pose proof (repr_len xd dep Hd) as LXd.
  fold nn in LXa. rewrite Hdl in LXd.
  unfold repr, repr_uint in Hx.
  assert (Xc : (φ x) = Z.of_N c) by (pose proof (to_Z_bounded x); lia).
  (* the math side of booking i *)
  set (amin := fun i : nat => zmin (nth i arr d0)).
  set (rmin := fun i : nat => (zmin (nth i dep d0) + Z.of_N c)%Z).
  set (al := fun i : nat => zal (amin i) (rmin i) (Z.of_nat i)).
  set (rh := fun i : nat => zrh (amin i) (rmin i) (Z.of_nat i)).
  assert (Hval : forall i, (i < nn)%nat ->
            valid_datetime (nth i arr d0) /\ valid_datetime (nth i dep d0)).
  { intros i Hi. rewrite Forall_forall in Varr, Vdep. split.
    - apply Varr. apply nth_In. exact Hi.
    - apply Vdep. apply nth_In. lia. }
  assert (Hmin : forall i, (i < nn)%nat ->
            amin i = Z.of_N (minutes (nth i arr d0)) /\
            rmin i = Z.of_N (minutes (nth i dep d0) + c) /\
            (0 <= amin i /\ amin i <= rmin i /\ rmin i <= 1100000360)%Z).
  { intros i Hi. destruct (Hval i Hi) as [V1 V2].
    pose proof (minutes_closed _ V1). pose proof (minutes_closed _ V2).
    pose proof (zmin_range _ V1). pose proof (zmin_range _ V2).
    pose proof (Forall2_nth_P _ _ _ d0 d0 Vord i Hi) as Hord. simpl in Hord.
    unfold amin, rmin. lia. }
  assert (Hne : forall j, In j (seq 0 nn) -> (al j < rh j)%Z).
  { intros j Hj. apply in_seq in Hj. destruct (Hmin j ltac:(lia)) as [_ [_ B]].
    apply key_nonempty; lia. }
  assert (ND : NoDup (map al (seq 0 nn))).
  { apply NoDup_map_inj; [apply seq_NoDup|]. intros i j Hi Hj E.
    apply in_seq in Hi, Hj.
    destruct (Hmin i ltac:(lia)) as [_ [_ Bi]]. destruct (Hmin j ltac:(lia)) as [_ [_ Bj]].
    pose proof (key_inj (amin i) (rmin i) (amin j) (rmin j) (Z.of_nat i) (Z.of_nat j) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) E). lia. }
  unfold min_rooms_impl.
  set (n := PArray.length xa) in *.
  assert (Hcell : forall k, ((φ k) < (φ n))%Z ->
     (φ (key_al (mach_minutes xa.[k]) (mach_minutes xd.[k] + x) k)) = al (Z.to_nat (φ k)) /\
     (φ (key_rh (mach_minutes xa.[k]) (mach_minutes xd.[k] + x) k)) = rh (Z.to_nat (φ k))).
  { intros k Hk. pose proof (to_Z_bounded k) as Bk.
    set (kk := Z.to_nat (φ k)).
    destruct (Hmin kk ltac:(unfold kk; lia)) as [_ [_ B]].
    destruct (Hval kk ltac:(unfold kk; lia)) as [V1 V2].
    assert (M1 : (φ (mach_minutes xa.[k])) = amin kk)
      by (apply mach_minutes_ok; [apply (repr_cell xa arr Ha); fold nn; lia | exact V1]).
    assert (M2 : (φ (mach_minutes xd.[k] + x)) = rmin kk).
    { pose proof (mach_minutes_ok (xd.[k]) (nth kk dep d0)
                    ltac:(apply (repr_cell xd dep Hd); rewrite Hdl; lia) V2) as M2.
      rewrite add_small; [|rewrite wB_val; fold kk in M2; unfold rmin in B; lia].
      rewrite M2, Xc. reflexivity. }
    assert (Kk : (φ k) = Z.of_nat kk) by (unfold kk; lia).
    rewrite key_al_ok, key_rh_ok by lia. rewrite M1, M2, Kk. split; reflexivity. }
  destruct (fill xa xd x n 0 (PArray.make n 0) (PArray.make n 0)
              (Zwf_well_founded 0 (gap n 0))) as [A R] eqn:EF.
  assert (Lmk : PArray.length (PArray.make n 0) = n).
  { rewrite alength_make. replace (n <=? PArray.max_length) with true; [reflexivity|].
    symmetry. apply leb_spec. rewrite max_length_val. lia. }
  destruct (fill_spec xa xd x n al rh Hcell _ 0 _ _ _ A R eq_refl
              ltac:(change (φ 0) with 0%Z; lia) Lmk Lmk
              ltac:(intros k' Hk'; change (φ 0) with 0%Z in Hk'; pose proof (to_Z_bounded k'); lia)
              EF) as [LA [LR CA]].
  assert (VA : view A = map al (seq 0 nn))
    by (apply view_eq; [rewrite LA; exact LXa | intros k' Hk'; rewrite LA in Hk'; apply CA; exact Hk']).
  assert (VR : view R = map rh (seq 0 nn))
    by (apply view_eq; [rewrite LR; exact LXa | intros k' Hk'; rewrite LR in Hk'; apply CA; exact Hk']).
  destruct (sort_all_spec A) as [[LA' [_ [_ PA]]] SA].
  destruct (sort_all_spec R) as [[LR' [_ [_ PR]]] SR].
  set (A' := sort_all A) in *. set (R' := sort_all R) in *.
  rewrite LA in SA, LA'. rewrite LR in SR, LR'. rewrite VA in PA. rewrite VR in PR.
  assert (Hsv := sweep_val_cntD A' R' n nn al rh LXa LA' LR' PA PR SA ND Hne).
  destruct (sweep_spec A' R' n LA' LR' SA SR _ 0 0 0
              (Zwf_well_founded 0 (meas n 0 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; lia) ltac:(change (φ 0) with 0%Z; lia)
              ltac:(change (φ 0) with 0%Z; lia)
              ltac:(intros _ m Hm; change (φ 0) with 0%Z in Hm; pose proof (to_Z_bounded m); lia)
              ltac:(left; reflexivity)
              ltac:(intros p' Hp'; change (φ 0) with 0%Z in Hp'; pose proof (to_Z_bounded p'); lia))
    as [Hex Hmax].
  set (r := sweep A' R' n 0 0 0 (Zwf_well_founded 0 (meas n 0 0))) in *.
  pose proof (to_Z_bounded r) as Br.
  (* every arrival key is a cell of A' *)
  assert (Hin : forall i, (i < nn)%nat -> exists p, ((φ p) < (φ n))%Z /\ (φ (A'.[p])) = al i).
  { intros i Hi.
    assert (In (al i) (view A'))
      by (apply (Permutation_in _ (Permutation_sym PA)); apply in_map; apply in_seq; lia).
    unfold view in H. rewrite LA', LXa, Nat2Z.id in H.
    apply in_map_iff in H. destruct H as [k [Ek Hk]]. apply in_seq in Hk.
    exists (of_Z (Z.of_nat k)).
    rewrite phi_of_nat by (rewrite wB_val; lia). split; [lia | exact Ek]. }
  (* compatibility is disjointness of the key intervals *)
  assert (Hcf : forall i j a1 d1 a2 d2,
     nth_error arr i = Some a1 -> nth_error dep i = Some d1 ->
     nth_error arr j = Some a2 -> nth_error dep j = Some d2 -> i <> j ->
     (compatible c a1 d1 a2 d2 <-> ~ conflict al rh i j)).
  { intros i j a1 d1 a2 d2 E1 E2 E3 E4 Hij.
    assert (Hi : (i < nn)%nat) by (apply nth_error_Some; congruence).
    assert (Hj : (j < nn)%nat) by (apply nth_error_Some; congruence).
    rewrite (nth_error_nth' arr d0 Hi) in E1. injection E1 as <-.
    assert (Hi' : (i < List.length dep)%nat) by lia.
    assert (Hj' : (j < List.length dep)%nat) by lia.
    rewrite (nth_error_nth' dep d0 Hi') in E2. injection E2 as <-.
    rewrite (nth_error_nth' arr d0 Hj) in E3. injection E3 as <-.
    rewrite (nth_error_nth' dep d0 Hj') in E4. injection E4 as <-.
    destruct (Hmin i Hi) as [Ai [Ri Bi]]. destruct (Hmin j Hj) as [Aj [Rj Bj]].
    pose proof (key_conflict (amin i) (rmin i) (amin j) (rmin j) (Z.of_nat i) (Z.of_nat j)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Kc.
    unfold conflict, compatible. fold (al i) (rh i) (al j) (rh j) in Kc.
    unfold al, rh in Kc |- *. rewrite Kc.
    split.
    - intros C F. apply F. lia.
    - intros F. destruct (Z_le_dec (rmin i) (amin j)) as [C|C]; [left; lia|].
      destruct (Z_le_dec (rmin j) (amin i)) as [C'|C']; [right; lia|].
      exfalso. apply F. lia. }
  exists (Z.to_N (φ r)). split; [reflexivity|]. split.
  - (* Z.to_N r rooms suffice: the greedy colouring *)
    destruct (cntD_upper al rh (Z.to_N (φ r)) nn (seq 0 nn)
                ltac:(rewrite length_seq; lia) (seq_NoDup _ _) Hne)
      as [room [Hr1 Hr2]].
    { intros i Hi. apply in_seq in Hi. destruct (Hin i ltac:(lia)) as [p [Hp Ep]].
      pose proof (Hmax p Hp). rewrite (Hsv p Hp), Ep in H. lia. }
    exists room. split.
    + intros i Hi. apply Hr1. apply in_seq. fold nn. lia.
    + intros i j a1 d1 a2 d2 E1 E2 E3 E4 Hij Heq.
      apply (Hcf i j a1 d1 a2 d2 E1 E2 E3 E4 Hij).
      assert (Hi : (i < nn)%nat) by (apply nth_error_Some; congruence).
      assert (Hj : (j < nn)%nat) by (apply nth_error_Some; congruence).
      apply Hr2; [apply in_seq; lia | apply in_seq; lia | exact Hij | exact Heq].
  - (* no fewer: the arrivals active at one key pairwise conflict *)
    intros k' [room [Hr1 Hr2]].
    destruct Hex as [H0 | [p [Hp Ep]]]; [rewrite H0; lia|].
    rewrite Ep, (Hsv p Hp).
    pose proof (cntD_lower al rh room k' (seq 0 nn) (seq_NoDup _ _)) as Hl.
    assert (Hle : (cntD al rh (φ (A'.[p])) (seq 0 nn) <= N.to_nat k')%nat).
    { apply Hl.
      - intros i Hi. apply in_seq in Hi. apply Hr1. fold nn. lia.
      - intros i j Hi Hj Hij Heq. apply in_seq in Hi, Hj.
        apply (Hcf i j (nth i arr d0) (nth i dep d0) (nth j arr d0) (nth j dep d0));
          [apply nth_error_nth'; lia .. | exact Hij |].
        apply (Hr2 i j); [apply nth_error_nth'; lia .. | exact Hij | exact Heq]. }
    lia.
Qed.

Definition min_rooms_correct :
  forall (c : N) (arr dep : list (datetime N))
         (x : uint) (xa xd : array (datetime uint)),
  valid_input c arr dep -> repr x c -> repr xa arr -> repr xd dep ->
  exists k : N, repr (min_rooms x xa xd) k /\ min_rooms_spec c arr dep k
  := min_rooms_impl_correct.
