(* Correctness proofs for bank_implem.v. *)
(* Implementation of bank (bank.spec).

   Code.  CLRS 16.5 / Problem 16-4: unit-time jobs with deadlines as a
   matroid greedy.
   - [p] := the permutation 0 .. n-1 of the persons (init_loop), sorted by
     cash, decreasing, with a top-down merge sort [msort] on the index
     array (scratch buffer [b], merge into the buffer, copy back).
   - L := min(t, n) minutes are enough: no schedule serves more than n
     persons, and the greedy places person i in the latest free minute
     <= min(t_i, L - 1).  The free minutes are a disjoint-set forest over
     the cells 0 .. L of one flat array [uf] (cell y + 1 is minute y, cell
     0 the sentinel "no free minute"); [find] follows parent pointers down
     to the root, the latest free cell <= its argument, and compresses the
     path; occupying cell r links it to r - 1.
   - the total cash collected is accumulated in a 63-bit int (at most
     10^4 * 10^5).

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) _] proof on a Z measure, as in template/polymul1.  Every
   array is threaded linearly.

   Proof.  Merge sort: segment lists [seg] and Permutation, sorted
   segments.  Union-find: [UFInv] ties the forest to a ghost owner map
   (cell -> person).  Optimality: at every prefix P of the sorted order,
   every valid schedule serves at most as many persons of P as the greedy
   accepted ([rank_state]: the classical rank bound m + #{i in P, d_i >= m}
   at m = the first free minute), then an Abel summation ([abel]) over the
   decreasing cash turns the prefix counts into the value bound. *)

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Permutation Sorted Bool.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Require Export bank_implem.
Open Scope uint63_scope.
Open Scope array_scope.


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

Lemma int_neq : forall x y : int, (φ x) <> (φ y) -> x <> y.
Proof. intros x y H E. apply H. rewrite E. reflexivity. Qed.

Lemma int_eq : forall x y : int, (φ x) = (φ y) -> x = y.
Proof. intros x y H. apply to_Z_inj. exact H. Qed.

(* Unfolding equations. *)

Lemma init_loop_eq : forall m k a H,
  init_loop m k a H =
  match bdec (k <? m) with
  | left Hk => init_loop m (k + 1) a.[k <- k] (Acc_inv H (dec_step m k Hk))
  | right _ => a
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma merge_loop_eq : forall cash src mid hi i j k dst H,
  merge_loop cash src mid hi i j k dst H =
  match bdec (k <? hi) with
  | left Hk =>
      if take_left cash src mid hi i j
      then merge_loop cash src mid hi (i + 1) j (k + 1) dst.[k <- src.[i]]
             (Acc_inv H (dec_step hi k Hk))
      else merge_loop cash src mid hi i (j + 1) (k + 1) dst.[k <- src.[j]]
             (Acc_inv H (dec_step hi k Hk))
  | right _ => dst
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma copy_loop_eq : forall src hi k dst H,
  copy_loop src hi k dst H =
  match bdec (k <? hi) with
  | left Hk => copy_loop src hi (k + 1) dst.[k <- src.[k]]
                 (Acc_inv H (dec_step hi k Hk))
  | right _ => dst
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma msort_eq : forall cash a b lo len H,
  msort cash a b lo len H =
  match bdec (1 <? len) with
  | left Hl =>
      let len1 := len / 2 in
      let mid := lo + len1 in
      let hi := lo + len in
      let (a1, b1) := msort cash a b lo len1 (Acc_inv H (dec_half len Hl)) in
      let (a2, b2) := msort cash a1 b1 mid (len - len1)
                        (Acc_inv H (dec_rest len Hl)) in
      let b3 := merge_loop cash a2 mid hi lo mid lo b2
                  (Zwf_well_founded 0 (gap hi lo)) in
      let a3 := copy_loop b3 hi lo a2 (Zwf_well_founded 0 (gap hi lo)) in
      (a3, b3)
  | right _ => (a, b)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma find_eq : forall a x H,
  find a x H =
  let p := a.[x] in
  match bdec (p <? x) with
  | left Hp =>
      let (a1, r) := find a p (Acc_inv H (dec_lt p x Hp)) in
      (a1.[x <- r], r)
  | right _ => (a, x)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma greedy_loop_eq : forall cash dl perm n L j uf tot H,
  greedy_loop cash dl perm n L j uf tot H =
  match bdec (j <? n) with
  | left Hj =>
      let i := perm.[j] in
      let d := dl.[i] in
      let c := if d <? L then d + 1 else L in
      let (uf1, r) := find uf c (Zwf_well_founded 0 (φ c)) in
      if r =? 0
      then greedy_loop cash dl perm n L (j + 1) uf1 tot
             (Acc_inv H (dec_step n j Hj))
      else greedy_loop cash dl perm n L (j + 1) uf1.[r <- r - 1] (tot + cash.[i])
             (Acc_inv H (dec_step n j Hj))
  | right _ => tot
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Segments of an array                                                *)
(* ------------------------------------------------------------------ *)

Lemma phi_of_Z : forall x : Z, (0 <= x < wB)%Z -> (φ (of_Z x)) = x.
Proof. intros x H. rewrite of_Z_spec. apply Z.mod_small. exact H. Qed.

(* the cells a.[lo], ..., a.[lo + len - 1] *)
Fixpoint seg (a : array int) (lo : Z) (len : nat) : list int :=
  match len with
  | O => []
  | S l => a.[of_Z lo] :: seg a (lo + 1) l
  end.

Lemma seg_length : forall a len lo, List.length (seg a lo len) = len.
Proof. intros a len. induction len as [| len IH]; intros lo; simpl; auto. Qed.

Lemma seg_app : forall a len1 len2 lo,
  seg a lo (len1 + len2) = seg a lo len1 ++ seg a (lo + Z.of_nat len1) len2.
Proof.
  intros a len1. induction len1 as [| len1 IH]; intros len2 lo; simpl.
  - rewrite Z.add_0_r. reflexivity.
  - rewrite IH. do 3 f_equal. lia.
Qed.

Lemma seg_ext : forall a b len lo, (0 <= lo)%Z -> (lo + Z.of_nat len <= wB)%Z ->
  (forall x : int, (lo <= (φ x) < lo + Z.of_nat len)%Z -> a.[x] = b.[x]) ->
  seg a lo len = seg b lo len.
Proof.
  intros a b len. induction len as [| len IH]; intros lo H0 H1 H; simpl; [reflexivity|].
  f_equal.
  - apply H. rewrite phi_of_Z by lia. lia.
  - apply IH; [lia | lia |]. intros x Hx. apply H. lia.
Qed.

(* appending the cell k to the segment lo .. k-1 *)
Lemma seg_snoc : forall a lo (k : int), (0 <= lo <= (φ k))%Z ->
  seg a lo (Z.to_nat ((φ k) + 1 - lo)) = seg a lo (Z.to_nat ((φ k) - lo)) ++ [a.[k]].
Proof.
  intros a lo k H.
  replace (Z.to_nat ((φ k) + 1 - lo)) with (Z.to_nat ((φ k) - lo) + 1)%nat by lia.
  rewrite seg_app. simpl. do 3 f_equal.
  replace (lo + Z.of_nat (Z.to_nat ((φ k) - lo)))%Z with (φ k) by lia.
  apply of_to_Z.
Qed.

Lemma seg_nth : forall a len lo k, (k < len)%nat ->
  nth k (seg a lo len) 0 = a.[of_Z (lo + Z.of_nat k)].
Proof.
  intros a len. induction len as [| len IH]; intros lo k Hk; [lia|].
  destruct k as [| k]; simpl.
  - rewrite Z.add_0_r. reflexivity.
  - rewrite IH by lia. do 2 f_equal. lia.
Qed.

Lemma perm_mid : forall (A B : list int) v,
  Permutation ((A ++ B) ++ [v]) ((A ++ [v]) ++ B).
Proof.
  intros A B v. rewrite <- !app_assoc. apply Permutation_app_head.
  apply Permutation_app_comm.
Qed.

(* ------------------------------------------------------------------ *)
(* Merge sort                                                          *)
(* ------------------------------------------------------------------ *)

(* a.[lo .. hi) is sorted by cash, decreasing *)
Definition sorted_on (cash a : array int) (lo hi : Z) : Prop :=
  forall x y : int, (lo <= (φ x))%Z -> ((φ x) <= (φ y))%Z -> ((φ y) < hi)%Z ->
    ((φ (cash.[a.[y]])) <= (φ (cash.[a.[x]])))%Z.

Lemma sorted_on_ext : forall cash a b lo hi,
  (forall x : int, (lo <= (φ x) < hi)%Z -> a.[x] = b.[x]) ->
  sorted_on cash a lo hi -> sorted_on cash b lo hi.
Proof.
  intros cash a b lo hi He Hs x y Hx Hxy Hy.
  rewrite <- (He x) by lia. rewrite <- (He y) by lia. apply Hs; lia.
Qed.

Lemma merge_spec : forall cash src mid hi lo,
  (0 <= (φ lo))%Z -> ((φ lo) <= (φ mid))%Z -> ((φ mid) <= (φ hi))%Z ->
  sorted_on cash src (φ lo) (φ mid) -> sorted_on cash src (φ mid) (φ hi) ->
  forall z i j k dst H, gap hi k = z ->
  ((φ lo) <= (φ i) <= (φ mid))%Z -> ((φ mid) <= (φ j) <= (φ hi))%Z ->
  ((φ k) - (φ lo) = ((φ i) - (φ lo)) + ((φ j) - (φ mid)))%Z ->
  ((φ hi) <= (φ (PArray.length dst)))%Z ->
  Permutation (seg dst (φ lo) (Z.to_nat ((φ k) - (φ lo))))
    (seg src (φ lo) (Z.to_nat ((φ i) - (φ lo))) ++ seg src (φ mid) (Z.to_nat ((φ j) - (φ mid)))) ->
  sorted_on cash dst (φ lo) (φ k) ->
  (forall x y : int, ((φ lo) <= (φ x) < (φ k))%Z ->
     (((φ i) <= (φ y) < (φ mid))%Z \/ ((φ j) <= (φ y) < (φ hi))%Z) ->
     ((φ (cash.[src.[y]])) <= (φ (cash.[dst.[x]])))%Z) ->
  let res := merge_loop cash src mid hi i j k dst H in
  PArray.length res = PArray.length dst /\
  Permutation (seg res (φ lo) (Z.to_nat ((φ hi) - (φ lo))))
    (seg src (φ lo) (Z.to_nat ((φ mid) - (φ lo))) ++ seg src (φ mid) (Z.to_nat ((φ hi) - (φ mid)))) /\
  sorted_on cash res (φ lo) (φ hi) /\
  (forall x : int, ((φ x) < (φ k) \/ (φ hi) <= (φ x))%Z -> res.[x] = dst.[x]).
Proof.
  intros cash src mid hi lo Hlo Hlm Hmh Hs1 Hs2 z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i j k dst H Hz Hi Hj Hk Hdl Hp Hsd Hdom res. subst res.
  rewrite merge_loop_eq.
  destruct (bdec (k <? hi)) as [Hkh | Hkh].
  - pose proof Hkh as Hkh'. rewrite ltb_spec in Hkh'.
    pose proof (to_Z_bounded k) as Bk.
    assert (Hk1 : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
    assert (Hkl : (k <? PArray.length dst) = true) by (rewrite ltb_spec; lia).
    destruct (take_left cash src mid hi i j) eqn:TL.
    + (* take src.[i] *)
      assert (Hi' : ((φ i) < (φ mid))%Z /\
                    (((φ j) < (φ hi))%Z -> ((φ (cash.[src.[j]])) <= (φ (cash.[src.[i]])))%Z)).
      { unfold take_left in TL.
        destruct (i <? mid) eqn:E1; [|discriminate]. rewrite ltb_spec in E1.
        split; [exact E1|]. intros Ej.
        assert (E2 : (j <? hi) = true) by (rewrite ltb_spec; exact Ej).
        rewrite E2 in TL. rewrite leb_spec in TL. exact TL. }
      destruct Hi' as [Him Hcmp].
      assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
      edestruct (IH (gap hi (k + 1)) ltac:(rewrite <- Hz; apply dec_step; exact Hkh)
                  (i + 1) j (k + 1) (dst.[k <- src.[i]]) (Acc_inv H (dec_step hi k Hkh))
                  eq_refl) as (R1 & R2 & R3 & R4);
        [ rewrite Hi1; lia | exact Hj | rewrite Hk1, Hi1; lia
        | rewrite alength_set; exact Hdl | | | | ].
      * rewrite Hk1, Hi1.
        rewrite (seg_snoc _ _ k) by lia. rewrite (seg_snoc src _ i) by lia.
        rewrite aget_set_same by exact Hkl.
        rewrite (seg_ext (dst.[k <- src.[i]]) dst);
          [ | lia | pose proof wB_val; lia
            | intros x Hx; apply aget_set_other; apply int_neq; lia ].
        eapply Permutation_trans; [apply Permutation_app_tail; exact Hp|].
        apply perm_mid.
      * rewrite Hk1. intros x y Hx Hxy Hy.
        destruct (Z.eq_dec (φ y) (φ k)) as [Ey | Ey].
        -- apply int_eq in Ey. subst y. rewrite aget_set_same by exact Hkl.
           destruct (Z.eq_dec (φ x) (φ k)) as [Ex | Ex].
           ++ apply int_eq in Ex. subst x. rewrite aget_set_same by exact Hkl. lia.
           ++ rewrite aget_set_other by (apply int_neq; lia).
              apply Hdom; lia.
        -- rewrite aget_set_other by (apply int_neq; lia).
           rewrite aget_set_other by (apply int_neq; lia).
           apply Hsd; lia.
      * rewrite Hk1, Hi1. intros x y Hx Hy.
        destruct (Z.eq_dec (φ x) (φ k)) as [Ex | Ex].
        -- apply int_eq in Ex. subst x. rewrite aget_set_same by exact Hkl.
           destruct Hy as [Hy | Hy].
           ++ apply Hs1; lia.
           ++ apply (Z.le_trans _ (φ (cash.[src.[j]]))); [apply Hs2; lia | apply Hcmp; lia].
        -- rewrite aget_set_other by (apply int_neq; lia).
           apply Hdom; lia.
      * split; [rewrite R1; apply alength_set|].
        split; [exact R2|]. split; [exact R3|].
        intros x Hx. rewrite R4 by (rewrite Hk1; lia).
        apply aget_set_other. apply int_neq. lia.
    + (* take src.[j] *)
      assert (Hj' : ((φ j) < (φ hi))%Z /\
                    (((φ i) < (φ mid))%Z -> ((φ (cash.[src.[i]])) < (φ (cash.[src.[j]])))%Z)).
      { unfold take_left in TL.
        destruct (i <? mid) eqn:E1.
        - rewrite ltb_spec in E1.
          destruct (j <? hi) eqn:E2; [|discriminate].
          rewrite ltb_spec in E2.
          rewrite <- not_true_iff_false, leb_spec in TL.
          split; [exact E2|]. intros _. lia.
        - rewrite <- not_true_iff_false, ltb_spec in E1. split; [lia|]. lia. }
      destruct Hj' as [Hjh Hcmp].
      assert (Hj1 : (φ (j + 1)) = ((φ j) + 1)%Z) by sia.
      edestruct (IH (gap hi (k + 1)) ltac:(rewrite <- Hz; apply dec_step; exact Hkh)
                  i (j + 1) (k + 1) (dst.[k <- src.[j]]) (Acc_inv H (dec_step hi k Hkh))
                  eq_refl) as (R1 & R2 & R3 & R4);
        [ exact Hi | rewrite Hj1; lia | rewrite Hk1, Hj1; lia
        | rewrite alength_set; exact Hdl | | | | ].
      * rewrite Hk1, Hj1.
        rewrite (seg_snoc _ _ k) by lia. rewrite (seg_snoc src _ j) by lia.
        rewrite aget_set_same by exact Hkl.
        rewrite (seg_ext (dst.[k <- src.[j]]) dst);
          [ | lia | pose proof wB_val; lia
            | intros x Hx; apply aget_set_other; apply int_neq; lia ].
        rewrite app_assoc. apply Permutation_app_tail. exact Hp.
      * rewrite Hk1. intros x y Hx Hxy Hy.
        destruct (Z.eq_dec (φ y) (φ k)) as [Ey | Ey].
        -- apply int_eq in Ey. subst y. rewrite aget_set_same by exact Hkl.
           destruct (Z.eq_dec (φ x) (φ k)) as [Ex | Ex].
           ++ apply int_eq in Ex. subst x. rewrite aget_set_same by exact Hkl. lia.
           ++ rewrite aget_set_other by (apply int_neq; lia).
              apply Hdom; lia.
        -- rewrite aget_set_other by (apply int_neq; lia).
           rewrite aget_set_other by (apply int_neq; lia).
           apply Hsd; lia.
      * rewrite Hk1, Hj1. intros x y Hx Hy.
        destruct (Z.eq_dec (φ x) (φ k)) as [Ex | Ex].
        -- apply int_eq in Ex. subst x. rewrite aget_set_same by exact Hkl.
           destruct Hy as [Hy | Hy].
           ++ assert (Hc := Hcmp ltac:(lia)).
              assert (Hc2 : ((φ (cash.[src.[y]])) <= (φ (cash.[src.[i]])))%Z) by (apply Hs1; lia).
              lia.
           ++ apply Hs2; lia.
        -- rewrite aget_set_other by (apply int_neq; lia).
           apply Hdom; lia.
      * split; [rewrite R1; apply alength_set|].
        split; [exact R2|]. split; [exact R3|].
        intros x Hx. rewrite R4 by (rewrite Hk1; lia).
        apply aget_set_other. apply int_neq. lia.
  - rewrite <- not_true_iff_false, ltb_spec in Hkh.
    assert (Ek : (φ k) = (φ hi)) by lia.
    assert (Ei : (φ i) = (φ mid)) by lia.
    assert (Ej : (φ j) = (φ hi)) by lia.
    rewrite Ek in Hp, Hsd. rewrite Ei, Ej in Hp.
    split; [reflexivity|]. split; [exact Hp|]. split; [exact Hsd|].
    intros; reflexivity.
Qed.

Lemma copy_spec : forall src hi z k dst H, gap hi k = z ->
  ((φ hi) <= (φ (PArray.length dst)))%Z ->
  let res := copy_loop src hi k dst H in
  PArray.length res = PArray.length dst /\
  (forall x : int, ((φ k) <= (φ x) < (φ hi))%Z -> res.[x] = src.[x]) /\
  (forall x : int, ((φ x) < (φ k) \/ (φ hi) <= (φ x))%Z -> res.[x] = dst.[x]).
Proof.
  intros src hi z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k dst H Hz Hdl res. subst res.
  rewrite copy_loop_eq.
  destruct (bdec (k <? hi)) as [Hkh | Hkh].
  - pose proof Hkh as Hkh'. rewrite ltb_spec in Hkh'.
    pose proof (to_Z_bounded k) as Bk.
    assert (Hk1 : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
    assert (Hkl : (k <? PArray.length dst) = true) by (rewrite ltb_spec; lia).
    edestruct (IH (gap hi (k + 1)) ltac:(rewrite <- Hz; apply dec_step; exact Hkh)
                (k + 1) (dst.[k <- src.[k]]) (Acc_inv H (dec_step hi k Hkh))
                eq_refl) as (R1 & R2 & R3);
      [ rewrite alength_set; exact Hdl | ].
    split; [rewrite R1; apply alength_set|].
    split.
    + intros x Hx. destruct (Z.eq_dec (φ x) (φ k)) as [Ex | Ex].
      * apply int_eq in Ex. subst x. rewrite R3 by (rewrite Hk1; lia).
        apply aget_set_same. exact Hkl.
      * apply R2. rewrite Hk1. lia.
    + intros x Hx. rewrite R3 by (rewrite Hk1; lia).
      apply aget_set_other. apply int_neq. lia.
  - rewrite <- not_true_iff_false, ltb_spec in Hkh.
    split; [reflexivity|]. split; [intros x Hx; lia | intros; reflexivity].
Qed.

Lemma msort_spec : forall cash z len a b lo H, (φ len) = z ->
  PArray.length b = PArray.length a ->
  (0 <= (φ lo))%Z -> ((φ lo) + (φ len) <= (φ (PArray.length a)))%Z ->
  let res := msort cash a b lo len H in
  PArray.length (fst res) = PArray.length a /\
  PArray.length (snd res) = PArray.length b /\
  Permutation (seg (fst res) (φ lo) (Z.to_nat (φ len)))
              (seg a (φ lo) (Z.to_nat (φ len))) /\
  sorted_on cash (fst res) (φ lo) ((φ lo) + (φ len)) /\
  (forall x : int, ((φ x) < (φ lo) \/ (φ lo) + (φ len) <= (φ x))%Z -> (fst res).[x] = a.[x]).
Proof.
  intros cash z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros len a b lo H Hz Hba Hlo Hhi res. subst res.
  pose proof (alength_bound a) as Ba. pose proof wB_val as WB.
  pose proof (to_Z_bounded len) as Bl.
  rewrite msort_eq.
  destruct (bdec (1 <? len)) as [Hl | Hl].
  - cbv zeta.
    pose proof Hl as Hl'. rewrite ltb_spec in Hl'. change (φ 1) with 1%Z in Hl'.
    assert (E1 : (φ (len / 2)) = ((φ len) / 2)%Z) by (rewrite div_spec; reflexivity).
    assert (E2 : (φ (len - len / 2)) = ((φ len) - (φ len) / 2)%Z) by sia.
    assert (Em : (φ (lo + len / 2)) = ((φ lo) + (φ len) / 2)%Z) by sia.
    assert (Eh : (φ (lo + len)) = ((φ lo) + (φ len))%Z) by sia.
    destruct (msort cash a b lo (len / 2) (Acc_inv H (dec_half len Hl)))
      as [a1 b1] eqn:M1.
    pose proof (IH (φ (len / 2)) ltac:(rewrite <- Hz; apply dec_half; exact Hl)
                  (len / 2) a b lo (Acc_inv H (dec_half len Hl)) eq_refl Hba Hlo
                  ltac:(lia)) as IH1.
    cbv zeta in IH1. rewrite M1 in IH1. simpl in IH1.
    destruct IH1 as (A1 & B1 & P1 & S1 & F1).
    destruct (msort cash a1 b1 (lo + len / 2) (len - len / 2)
                (Acc_inv H (dec_rest len Hl))) as [a2 b2] eqn:M2.
    pose proof (IH (φ (len - len / 2)) ltac:(rewrite <- Hz; apply dec_rest; exact Hl)
                  (len - len / 2) a1 b1 (lo + len / 2) (Acc_inv H (dec_rest len Hl))
                  eq_refl ltac:(rewrite A1, B1; exact Hba) ltac:(lia)
                  ltac:(rewrite A1; lia)) as IH2.
    cbv zeta in IH2. rewrite M2 in IH2. simpl in IH2.
    destruct IH2 as (A2 & B2 & P2 & S2 & F2).
    rewrite Em, E1, E2 in *.
    (* the left half is still sorted in a2 *)
    assert (S1' : sorted_on cash a2 (φ lo) ((φ lo) + (φ len) / 2)).
    { apply (sorted_on_ext cash a1); [|exact S1].
      intros x Hx. symmetry. apply F2. lia. }
    pose proof (merge_spec cash a2 (lo + len / 2) (lo + len) lo Hlo
                  ltac:(lia) ltac:(lia)
                  ltac:(rewrite Em; exact S1')
                  ltac:(rewrite Em, Eh; replace ((φ lo) + (φ len))%Z
                          with ((φ lo) + (φ len) / 2 + ((φ len) - (φ len) / 2))%Z by lia;
                        exact S2)
                  (gap (lo + len) lo) lo (lo + len / 2) lo b2
                  (Zwf_well_founded 0 (gap (lo + len) lo)) eq_refl
                  ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(rewrite B2, B1, Hba; lia)) as MS.
    edestruct MS as (MA & MP & MS' & MF).
    { rewrite Z.sub_diag, Em, Z.sub_diag. simpl. constructor. }
    { intros x y Hx Hxy Hy. lia. }
    { intros x y Hx Hy. lia. }
    clear MS.
    set (b3 := merge_loop cash a2 (lo + len / 2) (lo + len) lo (lo + len / 2) lo b2
                 (Zwf_well_founded 0 (gap (lo + len) lo))) in *.
    pose proof (copy_spec b3 (lo + len) (gap (lo + len) lo) lo a2
                  (Zwf_well_founded 0 (gap (lo + len) lo)) eq_refl
                  ltac:(rewrite A2, A1; lia)) as CS.
    cbv zeta in CS. destruct CS as (CA & CC & CF).
    set (a3 := copy_loop b3 (lo + len) lo a2 (Zwf_well_founded 0 (gap (lo + len) lo)))
      in *.
    simpl fst. simpl snd.
    rewrite Eh in MP, MS', CC, CF. rewrite Em in MP.
    split; [rewrite CA, A2, A1; reflexivity|].
    split; [rewrite MA, B2, B1; reflexivity|].
    split.
    + rewrite (seg_ext a3 b3); [| lia | lia | intros x Hx; apply CC; lia].
      replace ((φ lo) + (φ len) - (φ lo))%Z with (φ len) in MP by lia.
      eapply Permutation_trans; [exact MP|].
      replace (Z.to_nat (φ len))
        with (Z.to_nat ((φ len) / 2) + Z.to_nat ((φ len) - (φ len) / 2))%nat by lia.
      rewrite seg_app.
      replace ((φ lo) + Z.of_nat (Z.to_nat ((φ len) / 2)))%Z
        with ((φ lo) + (φ len) / 2)%Z by lia.
      replace ((φ lo) + (φ len) / 2 - (φ lo))%Z with ((φ len) / 2)%Z by lia.
      replace ((φ lo) + (φ len) - ((φ lo) + (φ len) / 2))%Z
        with ((φ len) - (φ len) / 2)%Z by lia.
      apply Permutation_app.
      * rewrite (seg_ext a2 a1); [exact P1 | lia | lia |].
        intros x Hx. apply F2. lia.
      * eapply Permutation_trans; [exact P2|].
        rewrite (seg_ext a1 a); [apply Permutation_refl | lia | lia |].
        intros x Hx. apply F1. lia.
    + split.
      * apply (sorted_on_ext cash b3); [|exact MS'].
        intros x Hx. symmetry. apply CC. lia.
      * intros x Hx. rewrite CF by lia. rewrite F2 by lia. apply F1. lia.
  - rewrite <- not_true_iff_false, ltb_spec in Hl. change (φ 1) with 1%Z in Hl.
    simpl fst. simpl snd.
    split; [reflexivity|]. split; [reflexivity|].
    split; [apply Permutation_refl|]. split; [|intros; reflexivity].
    intros x y Hx Hxy Hy.
    assert (x = y) by (apply int_eq; lia). subst y. lia.
Qed.

Lemma init_spec : forall m z k a H, gap m k = z ->
  ((φ m) <= (φ (PArray.length a)))%Z ->
  let res := init_loop m k a H in
  PArray.length res = PArray.length a /\
  (forall x : int, ((φ k) <= (φ x) < (φ m))%Z -> res.[x] = x) /\
  (forall x : int, ((φ x) < (φ k) \/ (φ m) <= (φ x))%Z -> res.[x] = a.[x]).
Proof.
  intros m z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k a H Hz Hdl res. subst res.
  rewrite init_loop_eq.
  destruct (bdec (k <? m)) as [Hkh | Hkh].
  - pose proof Hkh as Hkh'. rewrite ltb_spec in Hkh'.
    pose proof (to_Z_bounded k) as Bk.
    assert (Hk1 : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
    assert (Hkl : (k <? PArray.length a) = true) by (rewrite ltb_spec; lia).
    edestruct (IH (gap m (k + 1)) ltac:(rewrite <- Hz; apply dec_step; exact Hkh)
                (k + 1) (a.[k <- k]) (Acc_inv H (dec_step m k Hkh))
                eq_refl) as (R1 & R2 & R3);
      [ rewrite alength_set; exact Hdl | ].
    split; [rewrite R1; apply alength_set|].
    split.
    + intros x Hx. destruct (Z.eq_dec (φ x) (φ k)) as [Ex | Ex].
      * apply int_eq in Ex. subst x. rewrite R3 by (rewrite Hk1; lia).
        apply aget_set_same. exact Hkl.
      * apply R2. rewrite Hk1. lia.
    + intros x Hx. rewrite R3 by (rewrite Hk1; lia).
      apply aget_set_other. apply int_neq. lia.
  - rewrite <- not_true_iff_false, ltb_spec in Hkh.
    split; [reflexivity|]. split; [intros x Hx; lia | intros; reflexivity].
Qed.

(* ------------------------------------------------------------------ *)
(* Union-find over the cells 0 .. L                                    *)
(* ------------------------------------------------------------------ *)

(* The ghost owner map: cell y (minute y - 1) is given to person i. *)
Definition owner_map := Z -> option N.

Definition upd (o : owner_map) (r : Z) (v : option N) : owner_map :=
  fun y => if Z.eq_dec y r then v else o y.

(* cell 0 is the sentinel, always free *)
Definition free (o : owner_map) (y : Z) : Prop := y = 0%Z \/ o y = None.

Definition UFInv (uf : array int) (o : owner_map) (L : Z) : Prop :=
  (φ (PArray.length uf)) = (L + 1)%Z /\
  forall x : int, ((φ x) <= L)%Z ->
    ((φ (uf.[x])) <= (φ x))%Z /\
    ((φ (uf.[x])) = (φ x) <-> free o (φ x)) /\
    (forall y : Z, ((φ (uf.[x])) < y <= (φ x))%Z -> ~ free o y).

Lemma find_spec : forall o L z x a H, (φ x) = z ->
  UFInv a o L -> ((φ x) <= L)%Z ->
  let res := find a x H in
  UFInv (fst res) o L /\ ((φ (snd res)) <= (φ x))%Z /\ free o (φ (snd res)) /\
  (forall y : Z, ((φ (snd res)) < y <= (φ x))%Z -> ~ free o y).
Proof.
  intros o L z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros x a H Hz Hinv HxL res. subst res.
  rewrite find_eq. cbv zeta.
  destruct Hinv as [Hlen Hinv].
  destruct (Hinv x HxL) as (Hle & Hroot & Hgap).
  pose proof (to_Z_bounded x) as Bx.
  destruct (bdec (a.[x] <? x)) as [Hp | Hp].
  - pose proof Hp as Hp'. rewrite ltb_spec in Hp'.
    destruct (find a a.[x] (Acc_inv H (dec_lt a.[x] x Hp))) as [a1 r] eqn:F.
    pose proof (IH (φ (a.[x])) ltac:(rewrite <- Hz; apply dec_lt; exact Hp)
                  (a.[x]) a (Acc_inv H (dec_lt a.[x] x Hp)) eq_refl
                  (conj Hlen Hinv) ltac:(lia)) as IH1.
    cbv zeta in IH1. rewrite F in IH1. simpl in IH1.
    destruct IH1 as ([Hlen1 Hinv1] & Hr1 & Hr2 & Hr3).
    simpl fst. simpl snd.
    assert (Hnf : ~ free o (φ x)) by (rewrite <- Hroot; lia).
    assert (Hxl : (x <? PArray.length a1) = true) by (rewrite ltb_spec; lia).
    split; [split|].
    + rewrite alength_set. exact Hlen1.
    + intros x' Hx'. destruct (Z.eq_dec (φ x') (φ x)) as [E | E].
      * apply int_eq in E. subst x'. rewrite aget_set_same by exact Hxl.
        split; [lia|]. split.
        -- split; [intros; lia | intros F'; contradiction].
        -- intros y Hy. destruct (Z_le_gt_dec y (φ (a.[x]))) as [Hy' | Hy'].
           ++ apply Hr3. lia.
           ++ apply Hgap. lia.
      * rewrite aget_set_other by (apply int_neq; lia). apply Hinv1. exact Hx'.
    + split; [lia|]. split; [exact Hr2|].
      intros y Hy. destruct (Z_le_gt_dec y (φ (a.[x]))) as [Hy' | Hy'].
      * apply Hr3. lia.
      * apply Hgap. lia.
  - rewrite <- not_true_iff_false, ltb_spec in Hp.
    simpl fst. simpl snd.
    split; [exact (conj Hlen Hinv)|]. split; [lia|].
    split; [apply Hroot; lia|]. intros y Hy. lia.
Qed.

Lemma free_upd : forall o r i y, r <> 0%Z ->
  free (upd o r (Some i)) y <-> free o y /\ y <> r.
Proof.
  intros o r i y Hr. unfold free, upd.
  destruct (Z.eq_dec y r) as [E | E]; subst; split; intros H.
  - destruct H as [H | H]; [contradiction | discriminate].
  - destruct H; contradiction.
  - split; [exact H | exact E].
  - apply H.
Qed.

Lemma occupy_inv : forall uf o L (r : int) i,
  UFInv uf o L -> (1 <= (φ r) <= L)%Z -> o (φ r) = None ->
  UFInv (uf.[r <- r - 1]) (upd o (φ r) (Some i)) L.
Proof.
  intros uf o L r i [Hlen Hinv] Hr Hor.
  assert (Hr1 : (φ (r - 1)) = ((φ r) - 1)%Z) by sia.
  assert (Hrl : (r <? PArray.length uf) = true) by (rewrite ltb_spec; lia).
  split; [rewrite alength_set; exact Hlen|].
  intros x Hx. destruct (Z.eq_dec (φ x) (φ r)) as [E | E].
  - apply int_eq in E. subst x. rewrite aget_set_same by exact Hrl.
    rewrite Hr1. split; [lia|]. split.
    + rewrite free_upd by lia. split; [intros; lia | intros [_ F]; contradiction].
    + intros y Hy. rewrite free_upd by lia. intros [_ F]. lia.
  - rewrite aget_set_other by (apply int_neq; lia).
    destruct (Hinv x Hx) as (H1 & H2 & H3).
    split; [exact H1|]. split.
    + rewrite free_upd by lia. rewrite H2. tauto.
    + intros y Hy. rewrite free_upd by lia. intros [F _]. exact (H3 y Hy F).
Qed.

(* ------------------------------------------------------------------ *)
(* Schedules, owner maps and counting                                  *)
(* ------------------------------------------------------------------ *)

(* the cells a, a+1, ..., a+len-1 of an owner map, as a schedule *)
Fixpoint sched (o : owner_map) (a : Z) (len : nat) : schedule :=
  match len with
  | O => []
  | S l => o a :: sched o (a + 1) l
  end.

(* the persons owning one of those cells *)
Definition occ (o : owner_map) (a : Z) (len : nat) : list N := served (sched o a len).

Definition memS (s : schedule) (i : N) : bool :=
  if in_dec N.eq_dec i (served s) then true else false.

Definition cntb (l : list bool) : nat := List.length (filter (fun b => b) l).

Definition sumN (l : list N) : N := fold_right N.add 0%N l.

Fixpoint wsum (ws : list N) (bs : list bool) : N :=
  match ws, bs with
  | w :: ws', b :: bs' => ((if b then w else 0) + wsum ws' bs')%N
  | _, _ => 0%N
  end.

Lemma served_cons : forall o s,
  served (o :: s) = match o with Some i => [i] | None => [] end ++ served s.
Proof. reflexivity. Qed.

Lemma served_app : forall s1 s2, served (s1 ++ s2) = served s1 ++ served s2.
Proof. intros. unfold served. apply flat_map_app. Qed.

Lemma In_served : forall s i, In i (served s) -> exists k, nth_error s k = Some (Some i).
Proof.
  induction s as [| o s IH]; intros i H; simpl in H; [contradiction|].
  try rewrite served_cons in H. apply in_app_or in H. destruct H as [H | H].
  - destruct o as [j|]; simpl in H; [|contradiction].
    destruct H as [H | H]; [subst; exists O; reflexivity | contradiction].
  - destruct (IH i H) as [k Hk]. exists (S k). exact Hk.
Qed.

Lemma served_In : forall s i k, nth_error s k = Some (Some i) -> In i (served s).
Proof.
  induction s as [| o s IH]; intros i k H; [destruct k; discriminate|].
  try rewrite served_cons. apply in_or_app. destruct k as [| k]; simpl in H.
  - inversion H; subst. left. left. reflexivity.
  - right. exact (IH i k H).
Qed.

Lemma served_length : forall s, (List.length (served s) <= List.length s)%nat.
Proof.
  induction s as [| o s IH]; [simpl; lia|].
  rewrite served_cons, length_app. destruct o; simpl; lia.
Qed.

Lemma sched_length : forall o len a, List.length (sched o a len) = len.
Proof. intros o len. induction len as [| len IH]; intros a; simpl; auto. Qed.

Lemma sched_nth : forall o len a k, (k < len)%nat ->
  nth_error (sched o a len) k = Some (o (a + Z.of_nat k)%Z).
Proof.
  intros o len. induction len as [| len IH]; intros a k Hk; [lia|].
  destruct k as [| k]; simpl.
  - rewrite Z.add_0_r. reflexivity.
  - rewrite IH by lia. do 2 f_equal. lia.
Qed.

Lemma In_occ : forall o len a i,
  In i (occ o a len) <-> exists y, (a <= y < a + Z.of_nat len)%Z /\ o y = Some i.
Proof.
  intros o len. induction len as [| len IH]; intros a i; unfold occ; simpl.
  - split; [contradiction | intros (y & Hy & _); lia].
  - try rewrite served_cons. rewrite in_app_iff. fold (occ o (a + 1) len). rewrite IH.
    split.
    + intros [H | (y & Hy & Ho)].
      * destruct (o a) as [j|] eqn:E; simpl in H; [|contradiction].
        destruct H as [H | H]; [subst; exists a; split; [lia | exact E] | contradiction].
      * exists y. split; [lia | exact Ho].
    + intros (y & Hy & Ho). destruct (Z.eq_dec y a) as [E | E].
      * subst. left. rewrite Ho. left. reflexivity.
      * right. exists y. split; [lia | exact Ho].
Qed.

Lemma occ_app : forall o n1 n2 a,
  occ o a (n1 + n2) = occ o a n1 ++ occ o (a + Z.of_nat n1) n2.
Proof.
  intros o n1. induction n1 as [| n1 IH]; intros n2 a; unfold occ; simpl.
  - rewrite Z.add_0_r. reflexivity.
  - try rewrite !served_cons. fold (occ o (a + 1) (n1 + n2)). fold (occ o (a + 1) n1).
    rewrite IH, app_assoc. f_equal. unfold occ. do 2 f_equal. lia.
Qed.

Lemma occ_full : forall o len a,
  (forall y, (a <= y < a + Z.of_nat len)%Z -> o y <> None) ->
  List.length (occ o a len) = len.
Proof.
  intros o len. induction len as [| len IH]; intros a H; unfold occ; simpl; [reflexivity|].
  try rewrite served_cons. fold (occ o (a + 1) len). rewrite length_app.
  rewrite IH by (intros y Hy; apply H; lia).
  destruct (o a) eqn:E; [simpl; lia|]. exfalso. apply (H a); [lia | exact E].
Qed.

Lemma occ_ext : forall o o' len a,
  (forall y, (a <= y < a + Z.of_nat len)%Z -> o y = o' y) ->
  occ o a len = occ o' a len.
Proof.
  intros o o' len. induction len as [| len IH]; intros a H; unfold occ; simpl; [reflexivity|].
  try rewrite !served_cons. fold (occ o (a + 1) len). fold (occ o' (a + 1) len).
  rewrite H by lia. rewrite IH by (intros y Hy; apply H; lia). reflexivity.
Qed.

Lemma occ_upd : forall o len a r i,
  (a <= r < a + Z.of_nat len)%Z -> o r = None ->
  Permutation (occ (upd o r (Some i)) a len) (i :: occ o a len).
Proof.
  intros o len. induction len as [| len IH]; intros a r i Hr Hor; [lia|].
  unfold occ; simpl. try rewrite !served_cons.
  fold (occ o (a + 1) len). fold (occ (upd o r (Some i)) (a + 1) len).
  destruct (Z.eq_dec a r) as [E | E].
  - subst r. unfold upd at 1. destruct (Z.eq_dec a a) as [_ | F]; [|contradiction].
    rewrite Hor. simpl.
    rewrite (occ_ext (upd o a (Some i)) o); [apply Permutation_refl|].
    intros y Hy. unfold upd. destruct (Z.eq_dec y a); [lia | reflexivity].
  - unfold upd at 1. destruct (Z.eq_dec a r) as [F | _]; [contradiction|].
    eapply Permutation_trans; [apply Permutation_app_head; apply IH; [lia | exact Hor]|].
    apply Permutation_sym. apply Permutation_middle.
Qed.

Lemma occ_nodup : forall o len a,
  (forall y1 y2 i, o y1 = Some i -> o y2 = Some i -> y1 = y2) ->
  NoDup (occ o a len).
Proof.
  intros o len. induction len as [| len IH]; intros a Hinj; unfold occ; simpl;
    [constructor|].
  try rewrite served_cons. fold (occ o (a + 1) len).
  destruct (o a) as [i|] eqn:E; simpl; [|apply IH; exact Hinj].
  constructor; [|apply IH; exact Hinj].
  rewrite In_occ. intros (y & Hy & Ho).
  assert (y = a) by (apply (Hinj y a i Ho E)). lia.
Qed.

Lemma firstn_snoc : forall {A} (l : list A) j d, (j < List.length l)%nat ->
  firstn (S j) l = firstn j l ++ [nth j l d].
Proof.
  intros A l. induction l as [| x l IH]; intros j d Hj; simpl in Hj; [lia|].
  destruct j as [| j]; [reflexivity|].
  change (firstn (S (S j)) (x :: l)) with (x :: firstn (S j) l).
  rewrite (IH j d) by lia. reflexivity.
Qed.

Lemma cntb_app : forall l1 l2, cntb (l1 ++ l2) = (cntb l1 + cntb l2)%nat.
Proof. intros. unfold cntb. rewrite filter_app, length_app. reflexivity. Qed.

Lemma cntb_map : forall {A} (g : A -> bool) l,
  cntb (map g l) = List.length (filter g l).
Proof.
  intros A g l. induction l as [| x l IH]; [reflexivity|].
  simpl. unfold cntb in *. simpl. destruct (g x); simpl; lia.
Qed.

Lemma cntb_le : forall l, (cntb l <= List.length l)%nat.
Proof. intros. apply filter_length_le. Qed.

Lemma wsum_snoc : forall ws bs w b, List.length ws = List.length bs ->
  wsum (ws ++ [w]) (bs ++ [b]) = (wsum ws bs + if b then w else 0)%N.
Proof.
  induction ws as [| w' ws IH]; intros bs w b H; destruct bs as [| b' bs];
    simpl in H; try lia.
  - simpl. lia.
  - simpl. rewrite IH by lia. lia.
Qed.

Lemma wsum_filter : forall {A} (f : A -> N) (g : A -> bool) l,
  wsum (map f l) (map g l) = sumN (map f (filter g l)).
Proof.
  intros A f g l. induction l as [| x l IH]; [reflexivity|].
  simpl. rewrite IH. destruct (g x); simpl; lia.
Qed.

Lemma sumN_app : forall l1 l2, sumN (l1 ++ l2) = (sumN l1 + sumN l2)%N.
Proof. induction l1 as [| x l1 IH]; intros; simpl; [reflexivity|]. unfold sumN in *. rewrite IH. lia. Qed.

Lemma sumN_perm : forall l l', Permutation l l' -> sumN l = sumN l'.
Proof. intros l l' H. induction H; unfold sumN in *; simpl; lia. Qed.

Lemma wsum_firstn_all : forall ws bs, List.length bs = List.length ws ->
  wsum ws bs = wsum (firstn (List.length bs) ws) bs.
Proof. intros ws bs H. rewrite H, firstn_all. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Abel summation: prefix counts dominate => weighted sums dominate    *)
(* ------------------------------------------------------------------ *)

Lemma abel : forall ws xs bs (e : nat) (W : N),
  List.length xs = List.length ws -> List.length bs = List.length ws ->
  Forall (fun w => (w <= W)%N) ws ->
  StronglySorted (fun x y => (y <= x)%N) ws ->
  (forall k, (cntb (firstn k xs) <= e + cntb (firstn k bs))%nat) ->
  (wsum ws xs <= W * N.of_nat e + wsum ws bs)%N.
Proof.
  induction ws as [| w ws IH]; intros xs bs e W Hx Hb HW HS Hpre.
  - destruct xs; destruct bs; simpl; lia.
  - destruct xs as [| x xs]; [discriminate|]. destruct bs as [| b bs]; [discriminate|].
    simpl in Hx, Hb. inversion HS as [| ? ? HS' HF]; subst.
    inversion HW as [| ? ? HwW HW']; subst.
    assert (Hk : forall k, (cntb (firstn (S k) (x :: xs))
                  = (if x then 1 else 0) + cntb (firstn k xs))%nat
                 /\ (cntb (firstn (S k) (b :: bs))
                  = (if b then 1 else 0) + cntb (firstn k bs))%nat).
    { intros k. unfold cntb. simpl. destruct x, b; simpl; lia. }
    assert (H1 := Hpre 1%nat). destruct (Hk 0%nat) as [K1 K2].
    rewrite K1, K2 in H1. simpl in H1. unfold cntb in H1. simpl in H1.
    simpl.
    destruct x, b.
    + assert (IH1 := IH xs bs e w ltac:(lia) ltac:(lia) HF HS'
                 ltac:(intros k; destruct (Hk k) as [A1 A2];
                       specialize (Hpre (S k)); rewrite A1, A2 in Hpre; lia)).
      assert (w * N.of_nat e <= W * N.of_nat e)%N by (apply N.mul_le_mono_r; exact HwW).
      lia.
    + assert (IH1 := IH xs bs (e - 1)%nat w ltac:(lia) ltac:(lia) HF HS'
                 ltac:(intros k; destruct (Hk k) as [A1 A2];
                       specialize (Hpre (S k)); rewrite A1, A2 in Hpre; lia)).
      assert (w * N.of_nat e <= W * N.of_nat e)%N by (apply N.mul_le_mono_r; exact HwW).
      assert (E : (w * N.of_nat e = w * N.of_nat (e - 1)%nat + w)%N).
      { replace (N.of_nat e) with (N.of_nat (e - 1)%nat + 1)%N by lia. lia. }
      lia.
    + assert (IH1 := IH xs bs (e + 1)%nat w ltac:(lia) ltac:(lia) HF HS'
                 ltac:(intros k; destruct (Hk k) as [A1 A2];
                       specialize (Hpre (S k)); rewrite A1, A2 in Hpre; lia)).
      assert (w * N.of_nat e <= W * N.of_nat e)%N by (apply N.mul_le_mono_r; exact HwW).
      assert (E : (w * N.of_nat (e + 1)%nat = w * N.of_nat e + w)%N).
      { rewrite Nat2N.inj_add. lia. }
      lia.
    + assert (IH1 := IH xs bs e w ltac:(lia) ltac:(lia) HF HS'
                 ltac:(intros k; destruct (Hk k) as [A1 A2];
                       specialize (Hpre (S k)); rewrite A1, A2 in Hpre; lia)).
      assert (w * N.of_nat e <= W * N.of_nat e)%N by (apply N.mul_le_mono_r; exact HwW).
      lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The rank bound                                                      *)
(* ------------------------------------------------------------------ *)

Lemma filter_split_len : forall {A} (f g : A -> bool) l,
  List.length (filter f l) =
  (List.length (filter (fun x => f x && g x) l)
   + List.length (filter (fun x => f x && negb (g x)) l))%nat.
Proof.
  intros A f g l. induction l as [| x l IH]; [reflexivity|].
  simpl. destruct (f x), (g x); simpl; lia.
Qed.

Lemma filter_and_le : forall {A} (f g : A -> bool) l,
  (List.length (filter (fun x => f x && g x) l) <= List.length (filter g l))%nat.
Proof.
  intros A f g l. induction l as [| x l IH]; [simpl; lia|].
  simpl. destruct (f x), (g x); simpl; lia.
Qed.

Lemma memS_true : forall s i, memS s i = true -> In i (served s).
Proof. intros s i. unfold memS. destruct (in_dec N.eq_dec i (served s)); congruence. Qed.

Lemma memS_iff : forall s i, memS s i = true <-> In i (served s).
Proof.
  intros s i. unfold memS. destruct (in_dec N.eq_dec i (served s)); split; congruence || tauto.
Qed.

(* a valid schedule serves at most m persons with a deadline < m *)
Lemma rank_bound : forall t c d s, valid_schedule t c d s ->
  forall (P : list N) (m : nat), NoDup P ->
  (List.length (filter (memS s) P)
   <= m + List.length (filter (fun i => negb (Prelude.get d i <? N.of_nat m)%N) P))%nat.
Proof.
  intros t c d s Hs P m HP. destruct Hs as (Hlen & Hnd & Hk).
  rewrite (filter_split_len (memS s) (fun i => (Prelude.get d i <? N.of_nat m)%N)).
  assert (A : (List.length (filter (fun x => memS s x && (Prelude.get d x <? N.of_nat m)%N) P)
               <= m)%nat).
  { apply (Nat.le_trans _ (List.length (served (firstn m s)))).
    - apply NoDup_incl_length; [apply NoDup_filter; exact HP|].
      intros x Hx. apply filter_In in Hx. destruct Hx as [_ Hx].
      apply andb_prop in Hx. destruct Hx as [Hm Hd].
      apply memS_true, In_served in Hm. destruct Hm as [k Hk'].
      destruct (Hk k x Hk') as [_ Hkd]. apply N.ltb_lt in Hd.
      assert (Hkm : (k < m)%nat) by lia.
      assert (Hks : (k < List.length s)%nat) by (apply nth_error_Some; congruence).
      apply (served_In _ _ k).
      rewrite <- (firstn_skipn m s) in Hk'. rewrite nth_error_app1 in Hk'; [exact Hk'|].
      rewrite length_firstn. lia.
    - eapply Nat.le_trans; [apply served_length|]. apply firstn_le_length. }
  pose proof (filter_and_le (memS s) (fun i => negb (Prelude.get d i <? N.of_nat m)%N) P).
  lia.
Qed.

(* the latest minute person i may take among the L ones *)
Definition Dl (d : list N) (Lz : Z) (i : N) : Z := Z.min (Z.of_N (Prelude.get d i)) (Lz - 1)%Z.

Lemma dichotomy : forall (o : owner_map) len a,
  (forall y, (a <= y < a + Z.of_nat len)%Z -> o y <> None) \/
  exists m, (m < len)%nat /\ (forall y, (a <= y < a + Z.of_nat m)%Z -> o y <> None) /\
            o (a + Z.of_nat m)%Z = None.
Proof.
  intros o len a. induction len as [| len IH].
  - left. intros y Hy. lia.
  - destruct IH as [IH | (m & Hm & H1 & H2)].
    + destruct (o (a + Z.of_nat len)%Z) eqn:E.
      * left. intros y Hy. destruct (Z.eq_dec y (a + Z.of_nat len)) as [Ey | Ey].
        -- subst. rewrite E. discriminate.
        -- apply IH. lia.
      * right. exists len. split; [lia|]. split; [exact IH | exact E].
    + right. exists m. split; [lia|]. split; [exact H1 | exact H2].
Qed.

Lemma deadline_lt : forall t c d i, valid_input t c d -> (i < len c)%N ->
  (Prelude.get d i < t)%N.
Proof.
  intros t c d i Hv Hi. destruct Hv as [Hcol _ _ _ Hd].
  unfold len in Hcol, Hi. unfold Prelude.get.
  rewrite Forall_nth in Hd. apply Hd. lia.
Qed.

Lemma rank_state : forall t c d (Lz : Z) (o : owner_map) (P : list N) s,
  valid_input t c d -> Lz = Z.of_N (N.min t (len c)) -> NoDup P ->
  (forall i, In i P -> (i < len c)%N) -> (List.length P <= List.length c)%nat ->
  (forall y i, o y = Some i ->
     (1 <= y <= Lz)%Z /\ (y <= Dl d Lz i + 1)%Z /\
     (forall z, (y < z <= Dl d Lz i + 1)%Z -> o z <> None)) ->
  (forall i, In i P ->
     (exists y, o y = Some i) \/ (forall z, (1 <= z <= Dl d Lz i + 1)%Z -> o z <> None)) ->
  valid_schedule t c d s ->
  (List.length (filter (memS s) P) <= List.length (occ o 1 (Z.to_nat Lz)))%nat.
Proof.
  intros t c d Lz o P s Hv HL HP HPn HPl O1 O4 Hs.
  pose proof Hv as Hv'. destruct Hv' as [Hcol Hn Ht _ _]. unfold len in *.
  destruct (dichotomy o (Z.to_nat Lz) 1) as [Hall | (m & Hm & Hocc & Hfree)].
  - rewrite occ_full by (intros y Hy; apply Hall; exact Hy).
    destruct (N.le_gt_cases t (N.of_nat (List.length c))) as [Htn | Htn].
    + pose proof (rank_bound t c d s Hs P (N.to_nat t) HP) as RB.
      assert (E0 : List.length (filter (fun i => negb (Prelude.get d i <? N.of_nat (N.to_nat t))%N) P)
                   = 0%nat).
      { destruct (filter (fun i => negb (Prelude.get d i <? N.of_nat (N.to_nat t))%N) P)
          as [| x l] eqn:EF; [reflexivity|].
        exfalso. assert (Hx : In x (filter (fun i => negb (Prelude.get d i <? N.of_nat (N.to_nat t))%N) P))
          by (rewrite EF; left; reflexivity).
        apply filter_In in Hx. destruct Hx as [HxP Hx].
        apply negb_true_iff, N.ltb_ge in Hx.
        pose proof (deadline_lt t c d x Hv (HPn x HxP)). lia. }
      lia.
    + pose proof (filter_length_le (memS s) P). lia.
  - pose proof (rank_bound t c d s Hs P m HP) as RB.
    assert (Hsplit : List.length (occ o 1 (Z.to_nat Lz))
                     = (m + List.length (occ o (1 + Z.of_nat m) (Z.to_nat Lz - m)))%nat).
    { replace (Z.to_nat Lz) with (m + (Z.to_nat Lz - m))%nat at 1 by lia.
      rewrite occ_app, length_app, occ_full by (intros y Hy; apply Hocc; exact Hy).
      reflexivity. }
    assert (Hinc : (List.length (filter (fun i => negb (Prelude.get d i <? N.of_nat m)%N) P)
                    <= List.length (occ o (1 + Z.of_nat m) (Z.to_nat Lz - m)))%nat).
    { apply NoDup_incl_length; [apply NoDup_filter; exact HP|].
      intros i Hi. apply filter_In in Hi. destruct Hi as [HiP Hdi].
      apply negb_true_iff, N.ltb_ge in Hdi.
      assert (HD : (Z.of_nat m <= Dl d Lz i)%Z) by (unfold Dl; lia).
      destruct (O4 i HiP) as [(y & Hy) | Hrej].
      + destruct (O1 y i Hy) as (Hy1 & Hy2 & Hy3).
        apply In_occ. exists y. split; [|exact Hy].
        destruct (Z_le_gt_dec y (Z.of_nat m)) as [Hle | Hgt].
        * exfalso. apply (Hy3 (1 + Z.of_nat m)%Z); [lia | exact Hfree].
        * lia.
      + exfalso. apply (Hrej (1 + Z.of_nat m)%Z); [lia | exact Hfree]. }
    lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Small list facts                                                    *)
(* ------------------------------------------------------------------ *)

Lemma in_firstn : forall {A} k (l : list A) x, In x (firstn k l) -> In x l.
Proof.
  intros A k l x H. rewrite <- (firstn_skipn k l). apply in_or_app. left. exact H.
Qed.

Lemma nodup_firstn : forall {A} k (l : list A), NoDup l -> NoDup (firstn k l).
Proof.
  intros A k l H. rewrite <- (firstn_skipn k l) in H.
  apply NoDup_app_remove_r in H. exact H.
Qed.

Lemma nth_not_in_firstn : forall (l : list N) j, NoDup l -> (j < List.length l)%nat ->
  ~ In (nth j l 0%N) (firstn j l).
Proof.
  intros l j H Hj Hin.
  assert (E : nth_error l j = Some (nth j l 0%N)).
  { apply nth_error_nth'. exact Hj. }
  rewrite <- (firstn_skipn_middle j l E) in H.
  apply NoDup_remove_2 in H. apply H. apply in_or_app. left. exact Hin.
Qed.

Lemma occ_none : forall len a, occ (fun _ => None) a len = [].
Proof.
  intros len. induction len as [| len IH]; intros a; [reflexivity|].
  unfold occ. simpl. fold (occ (fun _ => None) (a + 1) len). apply IH.
Qed.

Lemma upd_not_none : forall o r i z, o z <> None -> upd o r (Some i) z <> None.
Proof.
  intros o r i z H. unfold upd. destruct (Z.eq_dec z r); [discriminate | exact H].
Qed.

Lemma nodup_map_of_nat : forall l, NoDup l -> NoDup (map N.of_nat l).
Proof.
  intros l H. induction H as [| x l Hx H IH]; simpl; constructor; [|exact IH].
  intros Hin. apply in_map_iff in Hin. destruct Hin as (y & Hy & Hin).
  apply Nat2N.inj in Hy. subst. contradiction.
Qed.

Lemma ss_of_nth : forall (l : list N),
  (forall i j, (i <= j < List.length l)%nat -> (nth j l 0 <= nth i l 0)%N) ->
  StronglySorted (fun a b => (b <= a)%N) l.
Proof.
  induction l as [| a l IH]; intros H; constructor.
  - apply IH. intros i j Hij. apply (H (S i) (S j)). simpl. lia.
  - apply Forall_forall. intros b Hb.
    destruct (In_nth l b 0%N Hb) as (k & Hk & Hnth).
    rewrite <- Hnth. apply (H O (S k)). simpl. lia.
Qed.

Lemma repr_uint_get : forall (a : array uint) (l : list N), repr a l ->
  forall k : int, ((φ k) < Z.of_nat (List.length l))%Z ->
  (φ (a.[k])) = Z.of_N (Prelude.get l (Z.to_N (φ k))).
Proof.
  intros a l [Hl Hc] k Hk.
  pose proof (to_Z_bounded k) as Bk.
  destruct (Hc (Z.to_nat (φ k)) ltac:(lia)) as (m & Hm & Hr).
  unfold repr, repr_uint in Hr.
  rewrite Z2Nat.id in Hr by lia. rewrite of_to_Z in Hr.
  unfold Prelude.get. rewrite Z_N_nat. rewrite (nth_error_nth _ _ 0%N Hm).
  rewrite <- Hr. pose proof (to_Z_bounded (a.[k])). lia.
Qed.

Lemma repr_uint_length : forall (a : array uint) (l : list N), repr a l ->
  (φ (PArray.length a)) = Z.of_nat (List.length l).
Proof. intros a l [Hl _]. symmetry. exact Hl. Qed.

(* ------------------------------------------------------------------ *)
(* The greedy loop                                                     *)
(* ------------------------------------------------------------------ *)

Section Greedy.

Variables (t : N) (c d : list N) (y z : array uint) (p : array int) (pl : list N)
          (Lm : int).

Hypothesis Hv : valid_input t c d.
Hypothesis Hy : repr y c.
Hypothesis Hz : repr z d.
Hypothesis Hpnd : NoDup pl.
Hypothesis Hplen : List.length pl = List.length c.
Hypothesis Hpin : forall i, In i pl -> (i < len c)%N.
Hypothesis Hpnth : forall j : int, ((φ j) < Z.of_nat (List.length c))%Z ->
  nth (Z.to_nat (φ j)) pl 0%N = Z.to_N (φ (p.[j])) /\
  ((φ (p.[j])) < Z.of_nat (List.length c))%Z.
Hypothesis HLm : (φ Lm) = Z.of_N (N.min t (len c)).

Definition Lz : Z := Z.of_N (N.min t (len c)).

Definition GInv (jn : nat) (uf : array int) (tot : int) (o : owner_map)
    (bs : list bool) : Prop :=
  UFInv uf o Lz /\
  (forall yy i, o yy = Some i ->
     (1 <= yy <= Lz)%Z /\ (yy <= Dl d Lz i + 1)%Z /\ In i (firstn jn pl) /\
     (forall zz, (yy < zz <= Dl d Lz i + 1)%Z -> o zz <> None)) /\
  (forall y1 y2 i, o y1 = Some i -> o y2 = Some i -> y1 = y2) /\
  (forall i, In i (firstn jn pl) ->
     (exists yy, o yy = Some i) \/
     (forall zz, (1 <= zz <= Dl d Lz i + 1)%Z -> o zz <> None)) /\
  List.length bs = jn /\
  cntb bs = List.length (occ o 1 (Z.to_nat Lz)) /\
  (φ tot) = Z.of_N (sumN (map (Prelude.get c) (occ o 1 (Z.to_nat Lz)))) /\
  (φ tot) = Z.of_N (wsum (firstn jn (map (Prelude.get c) pl)) bs) /\
  ((φ tot) <= 100000 * Z.of_nat jn)%Z /\
  (forall k, (k <= jn)%nat -> forall s, valid_schedule t c d s ->
     (List.length (filter (memS s) (firstn k pl)) <= cntb (firstn k bs))%nat).

(* the dominance at the new prefix, from the rank bound *)
Lemma dom_step : forall jn o,
  (jn <= List.length c)%nat ->
  (forall yy i, o yy = Some i ->
     (1 <= yy <= Lz)%Z /\ (yy <= Dl d Lz i + 1)%Z /\ In i (firstn jn pl) /\
     (forall zz, (yy < zz <= Dl d Lz i + 1)%Z -> o zz <> None)) ->
  (forall i, In i (firstn jn pl) ->
     (exists yy, o yy = Some i) \/
     (forall zz, (1 <= zz <= Dl d Lz i + 1)%Z -> o zz <> None)) ->
  forall s, valid_schedule t c d s ->
  (List.length (filter (memS s) (firstn jn pl)) <= List.length (occ o 1 (Z.to_nat Lz)))%nat.
Proof.
  intros jn o Hjn O1 O4 s Hs.
  apply (rank_state t c d Lz o (firstn jn pl) s Hv eq_refl).
  - apply nodup_firstn. exact Hpnd.
  - intros i Hi. apply Hpin. apply (in_firstn jn). exact Hi.
  - pose proof (firstn_le_length jn pl). lia.
  - intros yy i Ho. destruct (O1 yy i Ho) as (A & B & _ & D). auto.
  - exact O4.
  - exact Hs.
Qed.

Lemma cash_bound : forall i, (i < len c)%N -> (Prelude.get c i <= 100000)%N.
Proof.
  intros i Hi. destruct Hv as [_ _ _ Hc _]. unfold len in Hi. unfold Prelude.get.
  rewrite Forall_nth in Hc. apply Hc. lia.
Qed.

Lemma greedy_spec : forall zz j uf tot H o bs,
  gap (PArray.length y) j = zz ->
  (0 <= (φ j) <= Z.of_nat (List.length c))%Z ->
  GInv (Z.to_nat (φ j)) uf tot o bs ->
  exists uf' o' bs',
    GInv (List.length c) uf' (greedy_loop y z p (PArray.length y) Lm j uf tot H) o' bs'.
Proof.
  intros zz.
  induction zz as [zz IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j uf tot H o bs Hzz Hj Hinv.
  assert (Ly : (φ (PArray.length@{Set} y)) = Z.of_nat (List.length c))
    by exact (repr_uint_length y c Hy).
  pose proof Hv as Hv'. destruct Hv' as [Hcol Hn Ht _ _]. unfold len in Hcol, Hn, Ht.
  assert (Hdc : List.length d = List.length c) by lia.
  rewrite greedy_loop_eq.
  destruct (bdec (j <? PArray.length y)) as [Hjn | Hjn].
  - pose proof Hjn as Hjn'. rewrite ltb_spec, Ly in Hjn'.
    cbv zeta.
    set (jn := Z.to_nat (φ j)) in *.
    destruct (Hpnth j Hjn') as [Hnth Hpj]. fold jn in Hnth.
    set (iv := p.[j]) in *.
    set (i := Z.to_N (φ iv)) in *.
    assert (Hjl : (jn < List.length pl)%nat) by lia.
    assert (Hic : (i < len c)%N) by (unfold len, i; lia).
    assert (Hdi : (φ (@PArray.get@{Set} int z iv)) = Z.of_N (Prelude.get d i))
      by (exact (repr_uint_get z d Hz iv ltac:(lia))).
    assert (Hci : (φ (@PArray.get@{Set} int y iv)) = Z.of_N (Prelude.get c i))
      by (exact (repr_uint_get y c Hy iv ltac:(lia))).
    assert (Hdt : (Prelude.get d i < t)%N) by (apply deadline_lt with c; assumption).
    assert (Hcb : (Prelude.get c i <= 100000)%N) by (apply cash_bound; exact Hic).
    assert (HLz : (1 <= Lz)%Z) by (unfold Lz; lia).
    set (cv := if @PArray.get int z iv <? Lm then @PArray.get int z iv + 1 else Lm).
    assert (Hcv : (φ cv) = (Dl d Lz i + 1)%Z).
    { unfold cv, Dl. fold Lz in HLm.
      destruct (@PArray.get int z iv <? Lm) eqn:E.
      - rewrite ltb_spec in E. rewrite <- Hdi. pose proof (to_Z_bounded Lm).
        rewrite add_spec. change (φ 1) with 1%Z. rewrite Z.mod_small by lia. lia.
      - rewrite <- not_true_iff_false, ltb_spec in E. lia. }
    assert (Hcv0 : (0 <= Dl d Lz i)%Z) by (unfold Dl; lia).
    destruct Hinv as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10).
    pose proof (find_spec o Lz (φ cv) cv uf (Zwf_well_founded 0 (φ cv)) eq_refl I1
                  ltac:(rewrite Hcv; unfold Dl; lia)) as FS.
    cbv zeta in FS.
    destruct (find uf cv (Zwf_well_founded 0 (φ cv))) as [uf1 r] eqn:F.
    simpl in FS. destruct FS as (F1 & F2 & F3 & F4).
    rewrite Hcv in F2, F4.
    assert (Hj1 : (φ (j + 1)) = ((φ j) + 1)%Z) by sia.
    assert (Hjn1 : Z.to_nat (φ (j + 1)) = S jn) by (rewrite Hj1; unfold jn; lia).
    assert (Hfs : firstn (S jn) pl = firstn jn pl ++ [i]).
    { rewrite (firstn_snoc pl jn 0%N Hjl). rewrite Hnth. reflexivity. }
    assert (Hfsw : firstn (S jn) (map (Prelude.get c) pl)
                   = firstn jn (map (Prelude.get c) pl) ++ [Prelude.get c i]).
    { rewrite !firstn_map, Hfs, map_app. reflexivity. }
    assert (Hlfw : List.length (firstn jn (map (Prelude.get c) pl)) = List.length bs).
    { rewrite length_firstn, length_map. lia. }
    assert (Hdom_old : forall (bs' : list bool) b, bs' = bs ++ [b] ->
              forall k, (k <= jn)%nat -> firstn k bs' = firstn k bs).
    { intros bs' b E k Hk. subst bs'. rewrite firstn_app.
      replace (k - List.length bs)%nat with O by lia. simpl. apply app_nil_r. }
    destruct (r =? 0) eqn:R.
    + (* rejected *)
      rewrite Uint63.eqb_spec in R. subst r.
      change (φ 0) with 0%Z in F4.
      assert (Hrej : forall zz0, (1 <= zz0 <= Dl d Lz i + 1)%Z -> o zz0 <> None).
      { intros zz0 Hz0 E. apply (F4 zz0); [lia | right; exact E]. }
      assert (J2 : forall yy i', o yy = Some i' ->
                (1 <= yy <= Lz)%Z /\ (yy <= Dl d Lz i' + 1)%Z /\ In i' (firstn (S jn) pl) /\
                (forall zz0, (yy < zz0 <= Dl d Lz i' + 1)%Z -> o zz0 <> None)).
      { intros yy i' Ho. destruct (I2 yy i' Ho) as (A & B & C & D).
        rewrite Hfs. split; [exact A|]. split; [exact B|]. split; [|exact D].
        apply in_or_app. left. exact C. }
      assert (J4 : forall i', In i' (firstn (S jn) pl) ->
                (exists yy, o yy = Some i') \/
                (forall zz0, (1 <= zz0 <= Dl d Lz i' + 1)%Z -> o zz0 <> None)).
      { intros i' Hi'. rewrite Hfs in Hi'. apply in_app_or in Hi'.
        destruct Hi' as [Hi' | [Hi' | []]]; [apply I4; exact Hi'|].
        subst i'. right. exact Hrej. }
      eapply (IH (gap (PArray.length y) (j + 1))
                 ltac:(rewrite <- Hzz; apply dec_step; exact Hjn)
                 (j + 1) _ _ _ o (bs ++ [false]) eq_refl ltac:(rewrite Hj1; lia)).
      rewrite Hjn1.
      refine (conj F1 (conj J2 (conj I3 (conj J4 _)))).
      split; [rewrite length_app; simpl; lia|].
      split; [rewrite cntb_app; simpl; unfold cntb at 2; simpl; lia|].
      split; [exact I7|].
      split; [rewrite Hfsw, wsum_snoc by exact Hlfw; lia|].
      split; [lia|].
      intros k Hk s Hs.
      destruct (Nat.eq_dec k (S jn)) as [Ek | Ek].
      * subst k. rewrite (@firstn_all2 bool (S jn) (bs ++ [false])) by (rewrite length_app; simpl; lia).
        rewrite cntb_app. change (cntb [false]) with 0%nat.
        pose proof (dom_step (S jn) o ltac:(lia) J2 J4 s Hs). lia.
      * rewrite (Hdom_old (bs ++ [false]) false eq_refl k) by lia.
        apply I10; [lia | exact Hs].
    + (* accepted at cell r *)
      rewrite Uint63.eqb_false_spec in R.
      assert (Hr1 : (1 <= (φ r))%Z) by (pose proof (to_Z_bounded r); assert ((φ r) <> 0%Z) by (intro E; apply R; apply int_eq; exact E); lia).
      assert (Hor : o (φ r) = None) by (destruct F3 as [E | E]; [lia | exact E]).
      assert (Hrl : ((φ r) <= Lz)%Z) by (unfold Dl in F2; lia).
      assert (Hnew : ~ In i (firstn jn pl)).
      { rewrite <- Hnth. apply nth_not_in_firstn; assumption. }
      set (o' := upd o (φ r) (Some i)).
      assert (Ho'r : o' (φ r) = Some i) by (unfold o', upd; destruct (Z.eq_dec (φ r) (φ r)); [reflexivity | contradiction]).
      assert (Ho'n : forall yy, yy <> (φ r) -> o' yy = o yy)
        by (intros yy Hyy; unfold o', upd; destruct (Z.eq_dec yy (φ r)); [contradiction | reflexivity]).
      assert (Hmono : forall zz0, o zz0 <> None -> o' zz0 <> None)
        by (intros zz0 Hz0; apply upd_not_none; exact Hz0).
      assert (J2 : forall yy i', o' yy = Some i' ->
                (1 <= yy <= Lz)%Z /\ (yy <= Dl d Lz i' + 1)%Z /\ In i' (firstn (S jn) pl) /\
                (forall zz0, (yy < zz0 <= Dl d Lz i' + 1)%Z -> o' zz0 <> None)).
      { intros yy i' Ho. rewrite Hfs.
        destruct (Z.eq_dec yy (φ r)) as [E | E].
        - subst yy. rewrite Ho'r in Ho. injection Ho as <-.
          split; [lia|]. split; [lia|]. split; [apply in_or_app; right; left; reflexivity|].
          intros zz0 Hz0. apply Hmono. intros E. apply (F4 zz0); [lia | right; exact E].
        - rewrite Ho'n in Ho by exact E. destruct (I2 yy i' Ho) as (A & B & C & D).
          split; [exact A|]. split; [exact B|].
          split; [apply in_or_app; left; exact C|].
          intros zz0 Hz0. apply Hmono. apply D. exact Hz0. }
      assert (J3 : forall y1 y2 i', o' y1 = Some i' -> o' y2 = Some i' -> y1 = y2).
      { intros y1 y2 i' H1 H2.
        destruct (Z.eq_dec y1 (φ r)) as [E1 | E1]; destruct (Z.eq_dec y2 (φ r)) as [E2 | E2].
        - lia.
        - subst y1. rewrite Ho'r in H1. injection H1 as <-. rewrite Ho'n in H2 by exact E2.
          exfalso. apply Hnew. destruct (I2 y2 i H2) as (_ & _ & C & _). exact C.
        - subst y2. rewrite Ho'r in H2. injection H2 as <-. rewrite Ho'n in H1 by exact E1.
          exfalso. apply Hnew. destruct (I2 y1 i H1) as (_ & _ & C & _). exact C.
        - rewrite Ho'n in H1 by exact E1. rewrite Ho'n in H2 by exact E2.
          exact (I3 y1 y2 i' H1 H2). }
      assert (J4 : forall i', In i' (firstn (S jn) pl) ->
                (exists yy, o' yy = Some i') \/
                (forall zz0, (1 <= zz0 <= Dl d Lz i' + 1)%Z -> o' zz0 <> None)).
      { intros i' Hi'. rewrite Hfs in Hi'. apply in_app_or in Hi'.
        destruct Hi' as [Hi' | [Hi' | []]].
        - destruct (I4 i' Hi') as [(yy & Hyy) | Hrj].
          + left. exists yy. rewrite Ho'n; [exact Hyy|]. intros E. subst yy. congruence.
          + right. intros zz0 Hz0. apply Hmono. apply Hrj. exact Hz0.
        - subst i'. left. exists (φ r). exact Ho'r. }
      assert (Hperm : Permutation (occ o' 1 (Z.to_nat Lz)) (i :: occ o 1 (Z.to_nat Lz)))
        by (apply occ_upd; [lia | exact Hor]).
      assert (Htot : (φ (tot + @PArray.get int y iv)) = ((φ tot) + Z.of_N (Prelude.get c i))%Z).
      { rewrite add_spec, Hci. apply Z.mod_small. pose proof (to_Z_bounded tot).
        rewrite wB_val. lia. }
      eapply (IH (gap (PArray.length y) (j + 1))
                 ltac:(rewrite <- Hzz; apply dec_step; exact Hjn)
                 (j + 1) _ _ _ o' (bs ++ [true]) eq_refl ltac:(rewrite Hj1; lia)).
      rewrite Hjn1.
      refine (conj (occupy_inv uf1 o Lz r i F1 ltac:(lia) Hor)
                (conj J2 (conj J3 (conj J4 _)))).
      split; [rewrite length_app; simpl; lia|].
      split.
      { rewrite cntb_app. change (cntb [true]) with 1%nat.
        rewrite (Permutation_length Hperm). simpl. lia. }
      split.
      { rewrite Htot, I7. rewrite (sumN_perm _ _ (Permutation_map _ Hperm)). simpl. lia. }
      split; [rewrite Hfsw, wsum_snoc by exact Hlfw; rewrite Htot, I8; lia|].
      split; [rewrite Htot; lia|].
      intros k Hk s Hs.
      destruct (Nat.eq_dec k (S jn)) as [Ek | Ek].
      * subst k. rewrite (@firstn_all2 bool (S jn) (bs ++ [true])) by (rewrite length_app; simpl; lia).
        rewrite cntb_app. change (cntb [true]) with 1%nat.
        pose proof (dom_step (S jn) o' ltac:(lia) J2 J4 s Hs).
        rewrite (Permutation_length Hperm) in H0. cbn [List.length] in H0. lia.
      * rewrite (Hdom_old (bs ++ [true]) true eq_refl k) by lia.
        apply I10; [lia | exact Hs].
  - rewrite <- not_true_iff_false, ltb_spec, Ly in Hjn.
    exists uf, o, bs.
    replace (List.length c) with (Z.to_nat (φ j)) by lia. exact Hinv.
Qed.

End Greedy.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Lemma seg_id : forall a len lo, (0 <= lo)%Z -> (lo + Z.of_nat len <= wB)%Z ->
  (forall x : int, (lo <= (φ x) < lo + Z.of_nat len)%Z -> a.[x] = x) ->
  map (fun v => Z.to_N (φ v)) (seg a lo len) = map N.of_nat (seq (Z.to_nat lo) len).
Proof.
  intros a len. induction len as [| len IH]; intros lo H0 H1 H; [reflexivity|].
  simpl. f_equal.
  - rewrite H by (rewrite phi_of_Z by lia; lia). rewrite phi_of_Z by lia. lia.
  - rewrite IH by (try lia; intros x Hx; apply H; lia).
    replace (Z.to_nat (lo + 1)) with (S (Z.to_nat lo)) by lia. reflexivity.
Qed.

Lemma bank_impl_correct : forall (t : N) (c d : list N) (x : uint) (y z : array uint),
  valid_input t c d -> repr x t -> repr y c -> repr z d ->
  exists r : N, repr (bank_impl x y z) r /\ bank_spec t c d r.
Proof.
  intros t c d x y z Hv Hx Hy Hz.
  pose proof Hv as Hv'. destruct Hv' as [Hcol Hn Ht Hcash Hdl]. unfold len in Hcol, Hn.
  pose proof wB_val as WB.
  assert (Ly : (φ (PArray.length@{Set} y)) = Z.of_nat (List.length c))
    by exact (repr_uint_length y c Hy).
  assert (Hxt : (φ x) = Z.of_N t).
  { unfold repr, repr_uint in Hx. pose proof (to_Z_bounded x). lia. }
  unfold bank_impl. cbv zeta.
  set (n := PArray.length@{Set} y) in *.
  assert (Hmk : forall m : int, ((φ m) <= 4194303)%Z ->
            PArray.length (PArray.make m 0) = m).
  { intros m Hm. rewrite alength_make.
    replace (m <=? PArray.max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. exact Hm. }
  (* the identity permutation *)
  match goal with |- context [init_loop n 0 ?m0 ?H0] =>
    pose proof (init_spec n (gap n 0) 0 m0 H0 eq_refl
                  ltac:(rewrite Hmk by lia; lia)) as IS0;
    set (p0 := init_loop n 0 m0 H0) in * end.
  cbv zeta in IS0. destruct IS0 as (P0l & P0c & _).
  rewrite Hmk in P0l by lia.
  (* the sort *)
  match goal with |- context [msort y p0 ?b0 0 n ?H1] =>
    pose proof (msort_spec y (φ n) n p0 b0 0 H1 eq_refl
                  ltac:(rewrite P0l; apply Hmk; lia)
                  ltac:(change (φ 0) with 0%Z; lia)
                  ltac:(rewrite P0l; change (φ 0) with 0%Z; lia)) as MS;
    set (ps := msort y p0 b0 0 n H1) in * end.
  cbv zeta in MS. destruct MS as (MA & _ & MP & MSo & _).
  set (p := fst ps) in *.
  change (φ 0) with 0%Z in MP, MSo.
  assert (Hlen_n : Z.to_nat (φ n) = List.length c) by lia.
  rewrite Hlen_n in MP.
  (* the number of minutes *)
  set (Lm := if x <? n then x else n) in *.
  assert (HLm : (φ Lm) = Z.of_N (N.min t (len c))).
  { unfold Lm, len. destruct (x <? n) eqn:E;
      [rewrite ltb_spec in E | rewrite <- not_true_iff_false, ltb_spec in E]; lia. }
  assert (HL1 : (φ (Lm + 1)) = ((φ Lm) + 1)%Z) by (unfold len in HLm; sia).
  (* the union-find *)
  match goal with |- context [init_loop (Lm + 1) 0 ?m1 ?H2] =>
    pose proof (init_spec (Lm + 1) (gap (Lm + 1) 0) 0 m1 H2 eq_refl
                  ltac:(rewrite Hmk by (unfold len in HLm; lia); lia)) as IS1;
    set (uf0 := init_loop (Lm + 1) 0 m1 H2) in * end.
  cbv zeta in IS1. destruct IS1 as (U1l & U1c & _).
  rewrite Hmk in U1l by (unfold len in HLm; lia).
  assert (U0 : UFInv uf0 (fun _ => None) (Lz t c)).
  { unfold Lz. split; [rewrite U1l, HL1, HLm; reflexivity|].
    intros x' Hx'. rewrite U1c by (change (φ 0) with 0%Z; pose proof (to_Z_bounded x');
                                    rewrite HL1, HLm; lia).
    split; [lia|]. split; [split; intros; [right; reflexivity | reflexivity]|].
    intros; lia. }
  (* the sorted order of the persons *)
  set (pl := map (fun v => Z.to_N (φ v)) (seg p 0 (List.length c))).
  assert (Hid : map (fun v => Z.to_N (φ v)) (seg p0 0 (List.length c))
                = map N.of_nat (seq 0 (List.length c))).
  { apply (seg_id p0 (List.length c) 0); [lia | lia |].
    intros x' Hx'. apply P0c. change (φ 0) with 0%Z. lia. }
  assert (Hperm : Permutation pl (map N.of_nat (seq 0 (List.length c)))).
  { unfold pl. rewrite <- Hid. apply Permutation_map. exact MP. }
  assert (Hpnd : NoDup pl).
  { apply (Permutation_NoDup (Permutation_sym Hperm)).
    apply nodup_map_of_nat, seq_NoDup. }
  assert (Hplen : List.length pl = List.length c)
    by (unfold pl; rewrite length_map, seg_length; reflexivity).
  assert (Hpin : forall i, In i pl -> (i < len c)%N).
  { intros i Hi. apply (Permutation_in _ Hperm) in Hi.
    apply in_map_iff in Hi. destruct Hi as (k & <- & Hk).
    apply in_seq in Hk. unfold len. lia. }
  assert (Hpnth : forall j : int, ((φ j) < Z.of_nat (List.length c))%Z ->
            nth (Z.to_nat (φ j)) pl 0%N = Z.to_N (φ (p.[j])) /\
            ((φ (p.[j])) < Z.of_nat (List.length c))%Z).
  { intros j Hj. pose proof (to_Z_bounded j).
    assert (E : nth (Z.to_nat (φ j)) pl 0%N = Z.to_N (φ (p.[j]))).
    { unfold pl. change 0%N with ((fun v => Z.to_N (φ v)) 0).
      rewrite map_nth. rewrite seg_nth by lia.
      replace (0 + Z.of_nat (Z.to_nat (φ j)))%Z with (φ j) by lia.
      rewrite of_to_Z. reflexivity. }
    split; [exact E|].
    assert (Hin : In (Z.to_N (φ (p.[j]))) pl) by (rewrite <- E; apply nth_In; lia).
    apply Hpin in Hin. unfold len in Hin. pose proof (to_Z_bounded (p.[j])). lia. }
  (* the greedy loop *)
  match goal with |- context [greedy_loop ?cy ?dz p n Lm 0 uf0 0 ?H3] =>
    destruct (greedy_spec t c d y z p pl Lm Hv Hy Hz Hpnd Hplen Hpin Hpnth HLm
                (gap n 0) 0 uf0 0 H3 (fun _ => None) [] eq_refl
                ltac:(change (φ 0) with 0%Z; lia)) as (uf' & o & bs & G);
    [ | set (tot := greedy_loop cy dz p n Lm 0 uf0 0 H3) in * ] end.
  { change (Z.to_nat (φ 0)) with O.
    split; [exact U0|].
    split; [intros yy i E; discriminate|].
    split; [intros y1 y2 i E; discriminate|].
    split; [intros i Hi; simpl in Hi; contradiction|].
    split; [reflexivity|].
    split; [rewrite occ_none; reflexivity|].
    split; [rewrite occ_none; reflexivity|].
    split; [reflexivity|].
    split; [simpl; lia|].
    intros k Hk s Hs. replace k with O by lia. simpl. lia. }
  destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
  rewrite firstn_all2 in G2, G4, G8 by (try rewrite length_map; lia).
  assert (T7 : (φ tot) = Z.of_N (sumN (map (Prelude.get c) (occ o 1 (Z.to_nat (Lz t c))))))
    by exact G7.
  assert (T8 : (φ tot) = Z.of_N (wsum (map (Prelude.get c) pl) bs)) by exact G8.
  clear G7 G8 G9.
  exists (Z.to_N (φ tot)). split; [reflexivity|].
  assert (HLz : (1 <= Lz t c)%Z) by (unfold Lz, len; lia).
  split.
  - (* the greedy schedule collects tot *)
    exists (sched o 1 (Z.to_nat (Lz t c))).
    split; [split; [|split]|].
    + unfold len. rewrite sched_length. unfold Lz, len. lia.
    + apply occ_nodup. exact G3.
    + intros k i Hk.
      assert (Hkl : (k < Z.to_nat (Lz t c))%nat).
      { rewrite <- (sched_length o (Z.to_nat (Lz t c)) 1). apply nth_error_Some. congruence. }
      rewrite sched_nth in Hk by exact Hkl.
      assert (Hk2 : o (1 + Z.of_nat k)%Z = Some i) by congruence.
      clear Hk. rename Hk2 into Hk.
      destruct (G2 _ _ Hk) as (A & B & C & _).
      split; [apply Hpin; exact C|].
      unfold Dl in B. lia.
    + unfold value. fold (occ o 1 (Z.to_nat (Lz t c))). fold (sumN (map (Prelude.get c) (occ o 1 (Z.to_nat (Lz t c))))).
      lia.
  - (* no schedule collects more *)
    intros s Hs.
    pose proof Hs as Hs'. destruct Hs' as (_ & Hsnd & Hsk).
    assert (Hp : Permutation (served s) (filter (memS s) pl)).
    { apply NoDup_Permutation; [exact Hsnd | apply NoDup_filter; exact Hpnd |].
      intros i. rewrite filter_In, memS_iff. split; [|tauto].
      intros Hi. split; [|exact Hi].
      apply In_served in Hi. destruct Hi as [k Hk]. destruct (Hsk k i Hk) as [Hic _].
      apply (Permutation_in _ (Permutation_sym Hperm)). apply in_map_iff.
      exists (N.to_nat i). split; [lia|]. apply in_seq. unfold len in Hic. lia. }
    unfold value. fold (sumN (map (Prelude.get c) (served s))).
    rewrite (sumN_perm _ _ (Permutation_map _ Hp)).
    rewrite <- wsum_filter.
    assert (Ab := abel (map (Prelude.get c) pl) (map (memS s) pl) bs 0 100000
                   ltac:(rewrite !length_map; reflexivity)
                   ltac:(rewrite length_map; lia)).
    assert (Hfa : Forall (fun w => (w <= 100000)%N) (map (Prelude.get c) pl)).
    { apply Forall_forall. intros w Hw. apply in_map_iff in Hw. destruct Hw as (i & <- & Hi).
      apply (cash_bound t c d pl Lm Hv Hplen HLm). apply Hpin. exact Hi. }
    assert (Hget : forall k : int, ((φ k) < Z.of_nat (List.length c))%Z ->
              (φ (@PArray.get@{Set} int y k)) = Z.of_N (Prelude.get c (Z.to_N (φ k))))
      by (intros k Hk; exact (repr_uint_get y c Hy k Hk)).
    assert (Hnthp : forall b : nat, (b < List.length c)%nat ->
              nth b pl 0%N = Z.to_N (φ (@PArray.get@{Set} int p (of_Z (Z.of_nat b)))) /\
              ((φ (@PArray.get@{Set} int p (of_Z (Z.of_nat b)))) < Z.of_nat (List.length c))%Z).
    { intros b Hb.
      assert (Ej : (φ (of_Z (Z.of_nat b))) = Z.of_nat b) by (rewrite phi_of_Z; lia).
      destruct (Hpnth (of_Z (Z.of_nat b)) ltac:(rewrite Ej; lia)) as [N1 N2].
      rewrite Ej, Nat2Z.id in N1. split; [exact N1 | exact N2]. }
    assert (Hss : StronglySorted (fun a b => (b <= a)%N) (map (Prelude.get c) pl)).
    { apply ss_of_nth. rewrite length_map, Hplen. intros a b Hab.
      rewrite (nth_indep _ 0%N (Prelude.get c 0%N)) by (rewrite length_map; lia).
      rewrite (nth_indep (map (Prelude.get c) pl) 0%N (Prelude.get c 0%N))
        by (rewrite length_map; lia).
      rewrite !map_nth.
      destruct (Hnthp a ltac:(lia)) as [Na Ba]. destruct (Hnthp b ltac:(lia)) as [Nb Bb].
      rewrite Na, Nb.
      assert (Ea : (φ (of_Z (Z.of_nat a))) = Z.of_nat a) by (rewrite phi_of_Z; lia).
      assert (Eb : (φ (of_Z (Z.of_nat b))) = Z.of_nat b) by (rewrite phi_of_Z; lia).
      assert (S1 : ((φ (@PArray.get@{Set} int y (@PArray.get@{Set} int p (of_Z (Z.of_nat b)))))
                    <= (φ (@PArray.get@{Set} int y (@PArray.get@{Set} int p (of_Z (Z.of_nat a))))))%Z)
        by (exact (MSo (of_Z (Z.of_nat a)) (of_Z (Z.of_nat b))
                     ltac:(rewrite Ea; lia) ltac:(rewrite Ea, Eb; lia)
                     ltac:(rewrite Eb; lia))).
      rewrite (Hget _ Ba), (Hget _ Bb) in S1. lia. }
    assert (Hpre : forall k, (cntb (firstn k (map (memS s) pl)) <= 0 + cntb (firstn k bs))%nat).
    { intros k. rewrite firstn_map, cntb_map.
      destruct (Nat.le_gt_cases k (List.length c)) as [Hk | Hk];
        [apply G10; assumption|].
      rewrite (@firstn_all2 N k pl) by lia. rewrite (@firstn_all2 bool k bs) by lia.
      pose proof (G10 (List.length c) (le_n _) s Hs) as Gk.
      rewrite (@firstn_all2 N (List.length c) pl), (@firstn_all2 bool (List.length c) bs)
        in Gk by lia.
      lia. }
    specialize (Ab Hfa Hss Hpre). lia.
Qed.

Definition bank_correct :
  forall (t : N) (cash deadline : list N) (x : uint) (y z : array uint),
  valid_input t cash deadline ->
  repr x t -> repr y cash -> repr z deadline ->
  exists r : N, repr (bank x y z) r /\ bank_spec t cash deadline r
  := bank_impl_correct.
