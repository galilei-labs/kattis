(* Correctness proofs for kingpinescape_implem.v. *)
(* Implementation of kingpinescape (kingpinescape.spec): tree augmentation
   by leaf pairing.

   Code.  deg[v] is counted from the two columns (cnt_loop, once per
   column); pos = prefix sums of deg (pre_loop); the adjacency is a flat CSR
   table adj of the 2(n-1) half-edges (half-edge j < m is passageway j seen
   from ea[j], half-edge m + j the same passageway seen from eb[j]), filled
   by counting sort (fill_loop, once per column); after it, the slots of v
   are adj[pos[v] - deg[v] .. pos[v] - 1] and the other end of half-edge hh
   is [other].  The root is the first vertex of degree >= 2 (root_loop; 0
   when there is none, i.e. n = 2).  dfs_loop is the depth-first traversal
   with an explicit stack stk[0 .. sp-1] (a vertex is marked when pushed);
   every popped vertex of degree 1 is appended to lv, so lv lists the L
   leaves in visiting order.  The answer pairs lv[i] with lv[i + L/2] for
   i < L - L/2 (out_loop).  Every array is threaded linearly.  h is not
   read: making the network bridgeless is what the contract asks.

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) (gap _ _)] proof, as in template/polymul1.

   Proof.  The math side works over a "traversal" (Section Tree): the visiting
   order ord, ghost parent pointers par and parent passageways pe, with
   par(v) visited before v and, for consecutive vertices of ord, par of the
   later one an ancestor-or-self of the earlier one.  From that: pe is a
   bijection from the non-root vertices onto the passageways (pigeonhole,
   so the input is a simple tree without any use of route uniqueness),
   subtrees are contiguous in ord, leaves of a subtree are an interval of
   the leaf order, a proper non-empty interval is crossed by the pairing
   (cross), so every tree edge lies on a cycle (cross_edge) and the network
   is safe (tree_spec).  Minimality: a leaf's only passageway blocked, the
   leaf can only leave by a new passageway, so 2|F| >= L (leaf_needs).
   The machine side (Section Machine) proves each loop against those ghost
   objects (cnt_spec, pre_spec, fill_spec, nb_spec, dfs_spec, out_spec). *)

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Permutation.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Require Export kingpinescape_implem.
Open Scope uint63_scope.
Open Scope array_scope.


(* ------------------------------------------------------------------ *)
(* Uint63 / PArray plumbing                                            *)
(* ------------------------------------------------------------------ *)

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma max_length_val : (φ PArray.max_length) = 4194303%Z.
Proof. reflexivity. Qed.

(* a machine word read as an N, and an N as a machine word *)
Definition nv (x : int) : N := Z.to_N (φ x).
Definition ix (k : N) : int := of_Z (Z.of_N k).
(* cell k of an array, read as an N *)
Definition rd (a : array int) (k : N) : N := nv a.[ix k].

Lemma nv_Z : forall x, Z.of_N (nv x) = (φ x).
Proof. intros x. unfold nv. pose proof (to_Z_bounded x). lia. Qed.

Lemma nv_lt : forall x, (nv x < 9223372036854775808)%N.
Proof. intros x. unfold nv. pose proof (to_Z_bounded x). lia. Qed.

Lemma nv_inj : forall x y, nv x = nv y -> x = y.
Proof.
  intros x y H. apply to_Z_inj. rewrite <- !nv_Z, H. reflexivity.
Qed.

Lemma ix_nv : forall x, ix (nv x) = x.
Proof.
  intros x. unfold ix. rewrite nv_Z. apply of_to_Z.
Qed.

Lemma nv_ix : forall k, (k < 9223372036854775808)%N -> nv (ix k) = k.
Proof.
  intros k Hk. unfold nv, ix. rewrite of_Z_spec, Z.mod_small; [lia|].
  rewrite wB_val. lia.
Qed.

Lemma rd_nv : forall a x, rd a (nv x) = nv a.[x].
Proof. intros a x. unfold rd. rewrite ix_nv. reflexivity. Qed.

Lemma aget_set_same : forall (t : array int) (i : int) (b : int),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same int t i b H). Qed.

Lemma aget_set_other : forall (t : array int) (i j : int) (b : int),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other int t i j b H). Qed.

Lemma aget_make : forall (n i : int) (b : int), (PArray.make n b).[i] = b.
Proof. intros n i b. exact (get_make int b n i). Qed.

Lemma alength_set : forall (t : array int) (i : int) (b : int),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set int t i b). Qed.

Lemma alength_make : forall (n : int) (b : int),
  (nv n <= 4194303)%N -> nv (PArray.length (PArray.make n b)) = nv n.
Proof.
  intros n b Hn.
  assert (E : PArray.length (PArray.make n b)
              = if n <=? PArray.max_length then n else PArray.max_length)
    by exact (length_make int n b).
  assert (G : forall z, z = (if n <=? PArray.max_length then n else PArray.max_length)
                -> nv z = nv n).
  { intros z ->. replace (n <=? PArray.max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. rewrite <- nv_Z. lia. }
  apply G. exact E.
Qed.

Lemma alength_bound : forall (t : array int), (nv (PArray.length t) <= 4194303)%N.
Proof.
  intros t.
  assert (H : (PArray.length t <=? PArray.max_length) = true) by exact (leb_length int t).
  assert (G : forall z, (z <=? PArray.max_length) = true -> (nv z <= 4194303)%N).
  { intros z Hz. rewrite leb_spec, max_length_val in Hz. pose proof (nv_Z z). lia. }
  apply G. exact H.
Qed.

Lemma rd_set_same : forall (a : array int) i y k,
  k = nv i -> (k < nv (PArray.length a))%N -> rd a.[i <- y] k = nv y.
Proof.
  intros a i y k -> Hk. rewrite rd_nv. rewrite (aget_set_same a i y); [reflexivity|].
  rewrite ltb_spec, <- !nv_Z. lia.
Qed.

Lemma rd_set_other : forall (a : array int) i y k,
  (k < 9223372036854775808)%N -> k <> nv i -> rd a.[i <- y] k = rd a k.
Proof.
  intros a i y k Hk Hne. unfold rd. rewrite (aget_set_other a i (ix k) y); [reflexivity|].
  intro E. apply Hne. rewrite E, nv_ix by exact Hk. reflexivity.
Qed.

Lemma rd_make : forall n b k, rd (PArray.make n b) k = nv b.
Proof. intros n b k. unfold rd. rewrite aget_make. reflexivity. Qed.

Lemma nv_add : forall x y, ((φ x) + (φ y) < wB)%Z -> nv (x + y) = (nv x + nv y)%N.
Proof.
  intros x y H. unfold nv. rewrite add_spec, Z.mod_small; [|pose proof (to_Z_bounded x);
  pose proof (to_Z_bounded y); lia].
  pose proof (to_Z_bounded x); pose proof (to_Z_bounded y). lia.
Qed.

Lemma nv_add_N : forall x y, (nv x + nv y < 9223372036854775808)%N ->
  nv (x + y) = (nv x + nv y)%N.
Proof. intros x y H. apply nv_add. rewrite wB_val, <- !nv_Z. lia. Qed.

Lemma nv_sub : forall x y, (nv y <= nv x)%N -> nv (x - y) = (nv x - nv y)%N.
Proof.
  intros x y H. unfold nv in *. rewrite sub_spec, Z.mod_small;
  pose proof (to_Z_bounded x); pose proof (to_Z_bounded y); lia.
Qed.

Lemma ltb_nv : forall x y, (x <? y) = (nv x <? nv y)%N.
Proof.
  intros x y. destruct (x <? y) eqn:E; symmetry.
  - rewrite ltb_spec in E. apply N.ltb_lt.
    pose proof (nv_Z x); pose proof (nv_Z y). lia.
  - apply N.ltb_ge. rewrite <- Bool.not_true_iff_false, ltb_spec in E.
    pose proof (nv_Z x); pose proof (nv_Z y). lia.
Qed.

Lemma leb_nv : forall x y, (x <=? y) = (nv x <=? nv y)%N.
Proof.
  intros x y. destruct (x <=? y) eqn:E; symmetry.
  - rewrite leb_spec in E. apply N.leb_le.
    pose proof (nv_Z x); pose proof (nv_Z y). lia.
  - apply N.leb_gt. rewrite <- Bool.not_true_iff_false, leb_spec in E.
    pose proof (nv_Z x); pose proof (nv_Z y). lia.
Qed.

Lemma eqb_nv : forall x y, (x =? y) = (nv x =? nv y)%N.
Proof.
  intros x y. destruct (x =? y) eqn:E; symmetry.
  - rewrite eqb_spec in E. subst. apply N.eqb_refl.
  - apply N.eqb_neq. intro F. apply nv_inj in F. subst.
    rewrite eqb_refl in E. discriminate.
Qed.

Lemma nv_lsr1 : forall x, nv (x >> 1) = (nv x / 2)%N.
Proof.
  intros x. unfold nv. rewrite lsr_spec. change (2 ^ (φ 1))%Z with 2%Z.
  pose proof (to_Z_bounded x). rewrite Z2N.inj_div; [reflexivity | lia | lia].
Qed.

Lemma nv_0 : nv 0 = 0%N. Proof. reflexivity. Qed.
Lemma nv_1 : nv 1 = 1%N. Proof. reflexivity. Qed.
Lemma nv_2 : nv 2 = 2%N. Proof. reflexivity. Qed.

(* an array of length len l whose cells read as the elements of l *)
Definition arr_is (a : array int) (l : list N) : Prop :=
  nv (PArray.length a) = N.of_nat (List.length l) /\
  forall k, (k < List.length l)%nat -> rd a (N.of_nat k) = nth k l 0%N.

Lemma repr_arr_is : forall (x : array uint) (l : list N), repr x l -> arr_is x l.
Proof.
  intros x l [Hl Hc]. split.
  - unfold nv. change (PArray.length x) with (PArray.length@{repr_array.u0} x). lia.
  - intros k Hk. destruct (Hc k Hk) as (y & Hy & Hr).
    rewrite (nth_error_nth _ _ _ Hy).
    unfold repr, repr_uint in Hr. unfold rd, ix, nv.
    rewrite nat_N_Z. exact Hr.
Qed.

(* ------------------------------------------------------------------ *)
(* Routes: reaches is an equivalence, monotone in the passageways      *)
(* ------------------------------------------------------------------ *)

Open Scope N_scope.

Lemma joined_sym : forall E x y, joined E x y -> joined E y x.
Proof. unfold joined. tauto. Qed.

Lemma linked_cons : forall E x l,
  linked E (x :: l) <->
  (match l with [] => True | y :: _ => joined E x y end) /\ linked E l.
Proof. intros E x [| y l]; simpl; tauto. Qed.

Lemma linked_app_r : forall E p q, linked E (p ++ q) -> linked E q.
Proof.
  intros E p q. induction p as [| x p IH]; simpl; [tauto|].
  intros H. apply IH. apply linked_cons in H. tauto.
Qed.

Lemma linked_snoc : forall E l x y,
  linked E (l ++ [x]) -> joined E x y -> linked E (l ++ [x; y]).
Proof.
  intros E l x y. induction l as [| z l IH]; simpl.
  - intros _ H. tauto.
  - intros H J. apply linked_cons in H. apply linked_cons. destruct H as [H1 H2].
    split; [destruct l; exact H1 | exact (IH H2 J)].
Qed.

Lemma linked_rev : forall E l, linked E l -> linked E (rev l).
Proof.
  intros E l. induction l as [| x l IH]; simpl; [tauto|].
  intros H. apply linked_cons in H. destruct H as [H1 H2].
  destruct l as [| y l]; [simpl; tauto|].
  simpl in *. rewrite <- app_assoc. simpl. apply linked_snoc; [exact (IH H2)|].
  apply joined_sym. exact H1.
Qed.

Lemma linked_mono : forall E E' l, incl E E' -> linked E l -> linked E' l.
Proof.
  intros E E' l Hi. induction l as [| x l IH]; [simpl; tauto|].
  intros H. apply linked_cons in H. apply linked_cons. destruct H as [H1 H2].
  split; [| exact (IH H2)]. destruct l; [exact I|].
  unfold joined in *. destruct H1; [left | right]; apply Hi; assumption.
Qed.

Lemma hd_rev_cons : forall (x : N) l, l <> [] -> hd_error (rev (x :: l)) = hd_error (rev l).
Proof.
  intros x l Hl. simpl. destruct (rev l) eqn:E.
  - apply (f_equal (@rev N)) in E. rewrite rev_involutive in E. simpl in E. contradiction.
  - reflexivity.
Qed.

Lemma hd_rev_app : forall (p q : list N), q <> [] -> hd_error (rev (p ++ q)) = hd_error (rev q).
Proof.
  intros p q Hq. rewrite rev_app_distr. destruct (rev q) eqn:E.
  - apply (f_equal (@rev N)) in E. rewrite rev_involutive in E. simpl in E. contradiction.
  - reflexivity.
Qed.

Lemma route_rev : forall E u v l, route E u v l -> route E v u (rev l).
Proof.
  intros E u v l (H1 & H2 & H3 & H4). split; [apply NoDup_rev; exact H1|].
  split; [apply linked_rev; exact H2|]. rewrite rev_involutive. tauto.
Qed.

Lemma reaches_refl : forall E x, reaches E x x.
Proof.
  intros E x. exists [x]. split; [constructor; [simpl; tauto | constructor]|].
  simpl. tauto.
Qed.

Lemma reaches_sym : forall E x y, reaches E x y -> reaches E y x.
Proof. intros E x y [l Hl]. exists (rev l). apply route_rev. exact Hl. Qed.

Lemma reaches_mono : forall E E' x y, incl E E' -> reaches E x y -> reaches E' x y.
Proof.
  intros E E' x y Hi [l (H1 & H2 & H3 & H4)]. exists l.
  split; [exact H1|]. split; [exact (linked_mono E E' l Hi H2)|]. tauto.
Qed.

Lemma reaches_suffix : forall E a b l x, route E a b l -> In x l -> reaches E x b.
Proof.
  intros E a b l x (H1 & H2 & H3 & H4) Hx.
  destruct (in_split x l Hx) as (p & s & ->).
  exists (x :: s). split; [exact (NoDup_app_remove_l _ _ H1)|].
  split; [exact (linked_app_r E p _ H2)|].
  split; [reflexivity|]. rewrite <- H4. symmetry. apply hd_rev_app. discriminate.
Qed.

Lemma reaches_trans : forall E x y z, reaches E x y -> reaches E y z -> reaches E x z.
Proof.
  intros E x y z [l1 Hl1] [l2 Hl2].
  revert x Hl1. induction l1 as [| a l1 IH]; intros x Hl1.
  - destruct Hl1 as (_ & _ & H & _). discriminate.
  - pose proof Hl1 as (H1 & H2 & H3 & H4). simpl in H3. injection H3 as <-.
    destruct (in_dec N.eq_dec a l2) as [Ia | Na].
    + exact (reaches_suffix E y z l2 a Hl2 Ia).
    + destruct l1 as [| b l1].
      * simpl in H4. injection H4 as <-. exfalso. apply Na.
        destruct Hl2 as (_ & _ & G & _). destruct l2; [discriminate|].
        simpl in G. injection G as ->. left. reflexivity.
      * assert (Hr : route E b y (b :: l1)).
        { split; [inversion H1; assumption|].
          split; [apply linked_cons in H2; tauto|].
          split; [reflexivity|]. rewrite <- H4. symmetry. apply hd_rev_cons. discriminate. }
        destruct (IH b Hr) as [l Hl].
        destruct (in_dec N.eq_dec a l) as [Ia' | Na'].
        -- exact (reaches_suffix E b z l a Hl Ia').
        -- exists (a :: l). destruct Hl as (G1 & G2 & G3 & G4).
           split; [constructor; assumption|].
           split.
           ++ apply linked_cons. split; [| exact G2].
              destruct l as [| c l]; [discriminate|]. simpl in G3. injection G3 as ->.
              apply linked_cons in H2. tauto.
           ++ split; [reflexivity|]. rewrite <- G4. apply hd_rev_cons.
              intro E'. subst l. discriminate.
Qed.

Lemma joined_reaches : forall E x y, joined E x y -> reaches E x y.
Proof.
  intros E x y J. destruct (N.eq_dec x y) as [-> | Ne]; [apply reaches_refl|].
  exists [x; y]. split; [constructor; [simpl; intuition | constructor; [simpl; tauto | constructor]]|].
  simpl. tauto.
Qed.

(* reaching through E carries over to G when every passageway of E is
   bridged in G *)
Lemma reaches_bridge : forall E G x y,
  (forall a b, In (a, b) E -> reaches G a b) -> reaches E x y -> reaches G x y.
Proof.
  intros E G x y Hb [l (H1 & H2 & H3 & H4)]. clear H1.
  revert x H3. induction l as [| a l IH]; intros x H3; [discriminate|].
  simpl in H3. injection H3 as <-. apply linked_cons in H2. destruct H2 as [J H2].
  destruct l as [| b l].
  - simpl in H4. injection H4 as <-. apply reaches_refl.
  - apply reaches_trans with b.
    + destruct J as [J | J]; [exact (Hb _ _ J) | apply reaches_sym; exact (Hb _ _ J)].
    + apply IH; [exact H2 | | reflexivity]. rewrite <- H4. symmetry. apply hd_rev_cons. discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* Lists: positions, counts, blocking                                  *)
(* ------------------------------------------------------------------ *)

(* the position of x in l *)
Fixpoint idx (x : N) (l : list N) : nat :=
  match l with
  | [] => 0
  | y :: t => if N.eqb x y then 0 else S (idx x t)
  end.

Lemma idx_lt : forall x l, In x l -> (idx x l < List.length l)%nat.
Proof.
  intros x l. induction l as [| y l IH]; simpl; [tauto|].
  intros [-> | H]; [rewrite N.eqb_refl; lia|].
  destruct (N.eqb x y); [lia|]. specialize (IH H). lia.
Qed.

Lemma nth_idx : forall x l d, In x l -> nth (idx x l) l d = x.
Proof.
  intros x l d. induction l as [| y l IH]; simpl; [tauto|].
  intros [-> | H]; [rewrite N.eqb_refl; reflexivity|].
  destruct (N.eqb_spec x y); [subst; reflexivity|]. apply IH. exact H.
Qed.

Lemma idx_nth : forall l i d, NoDup l -> (i < List.length l)%nat -> idx (nth i l d) l = i.
Proof.
  intros l. induction l as [| y l IH]; intros i d Hn Hi; simpl in *; [lia|].
  inversion Hn as [| ? ? Hy Hl]; subst.
  destruct i as [| i]; [rewrite N.eqb_refl; reflexivity|].
  destruct (N.eqb_spec (nth i l d) y) as [E | E].
  - exfalso. apply Hy. rewrite <- E. apply nth_In. lia.
  - rewrite IH by (auto; lia). reflexivity.
Qed.

Lemma idx_app_l : forall x p q, In x p -> idx x (p ++ q) = idx x p.
Proof.
  intros x p q. induction p as [| y p IH]; simpl; [tauto|].
  intros [-> | H]; [rewrite N.eqb_refl; reflexivity|].
  destruct (N.eqb x y); [reflexivity|]. rewrite IH by exact H. reflexivity.
Qed.

Lemma idx_app_r : forall x p q, ~ In x p -> idx x (p ++ q) = (List.length p + idx x q)%nat.
Proof.
  intros x p q. induction p as [| y p IH]; simpl; [reflexivity|].
  intros H. destruct (N.eqb_spec x y); [exfalso; apply H; left; auto|].
  rewrite IH by tauto. reflexivity.
Qed.

Lemma idx_inj : forall l x y, In x l -> In y l -> idx x l = idx y l -> x = y.
Proof.
  intros l x y Hx Hy E. rewrite <- (nth_idx x l 0 Hx), <- (nth_idx y l 0 Hy), E.
  reflexivity.
Qed.

(* two positions of x in l *)
Lemma count_two : forall (l : list N) x,
  (2 <= count_occ N.eq_dec l x)%nat <->
  exists i i', (i < i' < List.length l)%nat /\ nth i l 0 = x /\ nth i' l 0 = x.
Proof.
  intros l x. induction l as [| y l IH]; simpl.
  - split; [lia|]. intros (i & i' & H & _). lia.
  - destruct (N.eq_dec y x) as [-> | Ne].
    + split.
      * intros H. assert (H1 : (1 <= count_occ N.eq_dec l x)%nat) by lia.
        apply (count_occ_In N.eq_dec) in H1. destruct (In_nth _ _ 0 H1) as (k & Hk & Ek).
        exists 0%nat, (S k). simpl. split; [lia|]. auto.
      * intros (i & i' & Hi & Ei & Ei').
        destruct i' as [| i']; [lia|]. simpl in Ei'.
        assert (H : In x l) by (rewrite <- Ei'; apply nth_In; simpl in Hi; lia).
        apply (count_occ_In N.eq_dec) in H. lia.
    + rewrite IH. split.
      * intros (i & i' & Hi & Ei & Ei'). exists (S i), (S i'). simpl. split; [lia|]. auto.
      * intros (i & i' & Hi & Ei & Ei').
        destruct i as [| i]; [simpl in Ei; contradiction|].
        destruct i' as [| i']; [lia|]. exists i, i'. simpl in *. split; [lia|]. auto.
Qed.

Lemma count_pos : forall (l : list N) x,
  (1 <= count_occ N.eq_dec l x)%nat <-> In x l.
Proof. intros l x. rewrite (count_occ_In N.eq_dec l x). lia. Qed.

Lemma nth_combine_N : forall (xs ys : list N) j,
  List.length xs = List.length ys -> nth j (combine xs ys) (0, 0) = (nth j xs 0, nth j ys 0).
Proof.
  intros xs ys j H. revert ys j H. induction xs as [| x xs IH]; intros [| y ys] j H;
    simpl in *; try discriminate; destruct j; auto.
Qed.

Lemma in_block : forall (E : list (N * N)) k p,
  In p (block E k) -> exists j, j <> k /\ (j < List.length E)%nat /\ nth j E (0, 0) = p.
Proof.
  intros E k p H. unfold block in H. apply in_app_or in H. destruct H as [H | H].
  - destruct (In_nth _ _ (0, 0) H) as (j & Hj & Ej). rewrite length_firstn in Hj.
    exists j. split; [lia|]. split; [lia|]. rewrite <- Ej. rewrite nth_firstn.
    destruct (Nat.ltb_spec j k); [reflexivity | lia].
  - destruct (In_nth _ _ (0, 0) H) as (j & Hj & Ej). rewrite length_skipn in Hj.
    exists (S k + j)%nat. split; [lia|]. split; [lia|]. rewrite <- Ej. rewrite nth_skipn.
    reflexivity.
Qed.

Lemma block_in : forall (E : list (N * N)) k j,
  j <> k -> (j < List.length E)%nat -> In (nth j E (0, 0)) (block E k).
Proof.
  intros E k j Hjk Hj. unfold block. apply in_or_app.
  destruct (Nat.ltb_spec j k).
  - left. assert (Ej : nth j E (0, 0) = nth j (firstn k E) (0, 0))
      by (rewrite nth_firstn; destruct (Nat.ltb_spec j k); [reflexivity | lia]).
    rewrite Ej. apply nth_In. rewrite length_firstn. lia.
  - right. replace j with (S k + (j - S k))%nat by lia. rewrite <- nth_skipn.
    apply nth_In. rewrite length_skipn. lia.
Qed.

Lemma block_app_l : forall (E F : list (N * N)) k,
  (k < List.length E)%nat -> block (E ++ F) k = block E k ++ F.
Proof.
  intros E F k Hk. unfold block. rewrite firstn_app, skipn_app.
  replace (k - List.length E)%nat with 0%nat by lia.
  replace (S k - List.length E)%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r, skipn_O, app_assoc. reflexivity.
Qed.

Lemma block_app_r : forall (E F : list (N * N)) k,
  (List.length E <= k)%nat -> incl E (block (E ++ F) k).
Proof.
  intros E F k Hk. unfold block. rewrite firstn_app.
  rewrite firstn_all2 by lia. intros p Hp. apply in_or_app. left. apply in_or_app. left. exact Hp.
Qed.

(* a duplicate-free list of hideouts below n has at most n elements *)
Lemma nodup_bound : forall (l : list N) n,
  NoDup l -> (forall x, In x l -> x < n) -> (List.length l <= N.to_nat n)%nat.
Proof.
  intros l n Hn Hb.
  assert (Hi : incl l (map N.of_nat (seq 0 (N.to_nat n)))).
  { intros x Hx. apply in_map_iff. exists (N.to_nat x). split; [lia|].
    apply in_seq. specialize (Hb x Hx). lia. }
  pose proof (NoDup_incl_length Hn Hi) as H. rewrite length_map, length_seq in H. exact H.
Qed.

(* m distinct values below m are all the values below m *)
Lemma pigeon : forall (l : list nat) m,
  NoDup l -> List.length l = m -> (forall x, In x l -> (x < m)%nat) ->
  forall j, (j < m)%nat -> In j l.
Proof.
  intros l m Hn Hl Hb j Hj.
  destruct (in_dec Nat.eq_dec j l) as [I | NI]; [exact I|]. exfalso.
  assert (Hi : incl l (remove Nat.eq_dec j (seq 0 m))).
  { intros x Hx. apply in_in_remove; [intros ->; contradiction|].
    apply in_seq. specialize (Hb x Hx). lia. }
  pose proof (NoDup_incl_length Hn Hi) as H.
  pose proof (remove_length_lt Nat.eq_dec (seq 0 m) j ltac:(apply in_seq; lia)) as H'.
  rewrite length_seq in H'. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The pairing crosses every proper interval of leaves                 *)
(* ------------------------------------------------------------------ *)

Lemma bounded_ex : forall (Q : nat -> Prop) c,
  (forall i, (i < c)%nat -> Q i \/ ~ Q i) ->
  (exists i, (i < c)%nat /\ Q i) \/ (forall i, (i < c)%nat -> ~ Q i).
Proof.
  intros Q c. induction c as [| c IH]; intros Hd.
  - right. intros i Hi. lia.
  - destruct IH as [(i & Hi & Qi) | Hn]; [intros i Hi; apply Hd; lia | |].
    + left. exists i. split; [lia | exact Qi].
    + destruct (Hd c ltac:(lia)) as [Qc | Nc].
      * left. exists c. split; [lia | exact Qc].
      * right. intros i Hi. destruct (Nat.eq_dec i c) as [-> | Ne]; [exact Nc|].
        apply Hn. lia.
Qed.

Lemma cross : forall (P : nat -> Prop) L,
  (forall i, (i < L)%nat -> P i \/ ~ P i) ->
  (forall i j k, (i < j < k)%nat -> (k < L)%nat -> P i -> P k -> P j) ->
  (exists i, (i < L)%nat /\ P i) -> (exists i, (i < L)%nat /\ ~ P i) ->
  exists i, (i < L - L / 2)%nat /\
    ((P i /\ ~ P (i + L / 2)%nat) \/ (~ P i /\ P (i + L / 2)%nat)).
Proof.
  intros P L Hd Hc (s & Hs & Ps) (w & Hw & Nw).
  set (a := (L / 2)%nat) in *.
  assert (Ha : (L = 2 * a \/ L = 2 * a + 1)%nat).
  { pose proof (Nat.div_mod L 2 ltac:(lia)) as D. pose proof (Nat.mod_upper_bound L 2 ltac:(lia)).
    fold a in D. lia. }
  assert (HL : (2 <= L)%nat) by (destruct (Nat.eq_dec s w); [subst; contradiction | lia]).
  destruct (bounded_ex (fun i => (P i /\ ~ P (i + a)%nat) \/ (~ P i /\ P (i + a)%nat))
              (L - a)) as [Hex | Hno].
  - intros i Hi. destruct (Hd i ltac:(lia)) as [Pi | Ni];
      destruct (Hd (i + a)%nat ltac:(lia)) as [Pj | Nj]; tauto.
  - exact Hex.
  - exfalso.
    assert (Eq : forall i, (i < L - a)%nat -> (P i <-> P (i + a)%nat)).
    { intros i Hi. specialize (Hno i Hi).
      destruct (Hd i ltac:(lia)) as [Pi | Ni];
        destruct (Hd (i + a)%nat ltac:(lia)) as [Pj | Nj]; tauto. }
    destruct (Hd 0%nat ltac:(lia)) as [P0 | N0].
    + assert (Pa : P a) by (apply (Eq 0%nat ltac:(lia)); exact P0).
      assert (Low : forall j, (j <= a)%nat -> P j).
      { intros j Hj. destruct (Nat.eq_dec j 0) as [-> | N1]; [exact P0|].
        destruct (Nat.eq_dec j a) as [-> | N2]; [exact Pa|].
        apply (Hc 0%nat j a); [lia | lia | exact P0 | exact Pa]. }
      apply Nw. destruct (Nat.le_gt_cases w a) as [Hwa | Hwa]; [apply Low; exact Hwa|].
      replace w with ((w - a) + a)%nat by lia.
      apply (Eq (w - a)%nat ltac:(lia)). apply Low. lia.
    + assert (Na : ~ P a) by (intro Pa; apply N0; apply (Eq 0%nat ltac:(lia)); exact Pa).
      apply Na. destruct (Nat.eq_dec s a) as [-> | Nsa]; [exact Ps|].
      assert (s <> 0%nat) by (intros ->; contradiction).
      destruct (Nat.ltb_spec s (L - a)) as [Hsc | Hsc].
      * assert (Psa : P (s + a)%nat) by (apply (Eq s Hsc); exact Ps).
        apply (Hc s a (s + a)%nat); [lia | lia | exact Ps | exact Psa].
      * assert (Psa : P (s - a)%nat).
        { apply (Eq (s - a)%nat ltac:(lia)). replace (s - a + a)%nat with s by lia. exact Ps. }
        destruct (Nat.eq_dec (s - a) a) as [E | E]; [rewrite <- E; exact Psa|].
        apply (Hc (s - a)%nat a s); [lia | lia | exact Psa | exact Ps].
Qed.

(* ------------------------------------------------------------------ *)
(* The traversal tree: ancestors                                       *)
(* ------------------------------------------------------------------ *)

(* a is an ancestor of y, or y itself, following the parent pointers par
   from y up to the root r *)
Inductive anc (par : N -> N) (r a : N) : N -> Prop :=
| anc_refl : anc par r a a
| anc_step : forall y, y <> r -> anc par r a (par y) -> anc par r a y.

Lemma anc_trans : forall par r a b c, anc par r a b -> anc par r b c -> anc par r a c.
Proof.
  intros par r a b c H1 H2. induction H2 as [| y Hy H IH]; [exact H1|].
  apply anc_step; assumption.
Qed.

Lemma anc_inv : forall par r a y, anc par r a y -> y <> a -> y <> r /\ anc par r a (par y).
Proof. intros par r a y H Hne. destruct H as [| y Hy H]; [contradiction | auto]. Qed.

Lemma anc_par : forall par r y, anc par r (par y) y \/ y = r.
Proof.
  intros par r y. destruct (N.eq_dec y r) as [-> | Ne]; [right; reflexivity|].
  left. apply anc_step; [exact Ne | apply anc_refl].
Qed.

Lemma anc_total : forall par r a b x, anc par r a x -> anc par r b x ->
  anc par r a b \/ anc par r b a.
Proof.
  intros par r a b x H1. revert b. induction H1 as [| y Hy H IH]; intros b H2.
  - right. exact H2.
  - inversion H2 as [E | y' Hy' H' E]; subst.
    + left. apply anc_step; assumption.
    + apply IH. exact H'.
Qed.

(* the frame: changing par outside a set closed under par keeps ancestry *)
Lemma anc_frame : forall par par' r (X : N -> Prop) a b,
  (forall x, X x -> par' x = par x) ->
  (forall x, X x -> x <> r -> X (par x)) ->
  X b -> anc par r a b -> anc par' r a b.
Proof.
  intros par par' r X a b Hp Hc Hb H. induction H as [| y Hy H IH]; [apply anc_refl|].
  apply anc_step; [exact Hy|]. rewrite Hp by exact Hb. apply IH. apply Hc; assumption.
Qed.

Lemma nodup_map_inj : forall (f : N -> nat) (l : list N),
  NoDup l -> (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup (map f l).
Proof.
  intros f l. induction l as [| x l IH]; intros Hn Hi; simpl; [constructor|].
  inversion Hn as [| ? ? Hx Hl]; subst. constructor.
  - intros H. apply in_map_iff in H. destruct H as (y & Ey & Iy).
    assert (x = y) by (apply Hi; simpl; auto). subst. contradiction.
  - apply IH; [exact Hl|]. intros u v Hu Hv. apply Hi; simpl; auto.
Qed.

Lemma filter_order : forall (f : N -> bool) l i j,
  NoDup l -> (i < j < List.length (filter f l))%nat ->
  (idx (nth i (filter f l) 0%N) l < idx (nth j (filter f l) 0%N) l)%nat.
Proof.
  intros f l. induction l as [| x l IH]; intros i j Hn Hij; [simpl in Hij; lia|].
  inversion Hn as [| ? ? Hx Hl]; subst.
  assert (Hin : forall k, (k < List.length (filter f l))%nat -> In (nth k (filter f l) 0) l).
  { intros k Hk. apply (filter_In f). apply nth_In. exact Hk. }
  assert (Hne : forall k, (k < List.length (filter f l))%nat ->
            idx (nth k (filter f l) 0) (x :: l) = S (idx (nth k (filter f l) 0) l)).
  { intros k Hk. simpl. destruct (N.eqb_spec (nth k (filter f l) 0) x) as [E | E];
      [exfalso; apply Hx; rewrite <- E; apply Hin; exact Hk | reflexivity]. }
  simpl in Hij |- *. destruct (f x).
  - simpl in Hij. destruct i as [| i]; destruct j as [| j]; try lia.
    + simpl. rewrite N.eqb_refl. destruct (N.eqb_spec (nth j (filter f l) 0) x) as [E | E];
        [exfalso; apply Hx; rewrite <- E; apply Hin; lia | lia].
    + specialize (IH i j Hl ltac:(lia)).
      pose proof (Hne i ltac:(lia)) as E1. pose proof (Hne j ltac:(lia)) as E2.
      simpl in E1, E2 |- *. rewrite E1, E2. lia.
  - specialize (IH i j Hl Hij).
    pose proof (Hne i ltac:(lia)) as E1. pose proof (Hne j ltac:(lia)) as E2.
    simpl in E1, E2. rewrite E1, E2. lia.
Qed.

(* the degree of v: the number of passageway ends at v *)
Definition deg (ea eb : list N) (v : N) : nat := count_occ N.eq_dec (ea ++ eb) v.

(* passageway j has an end at x *)
Definition endp (ea eb : list N) (j : nat) (x : N) : Prop :=
  nth j ea 0 = x \/ nth j eb 0 = x.

Lemma list_hd_tl : forall (l : list N) k, List.length l = S k -> l = nth 0 l 0 :: tl l.
Proof. intros [| x l] k H; [discriminate | reflexivity]. Qed.

(* ------------------------------------------------------------------ *)
(* The lower bound: every leaf needs a new passageway                  *)
(* ------------------------------------------------------------------ *)

Lemma leaf_needs : forall (n h : N) (ea eb : list N) F,
  valid_input n h ea eb -> safe n h (combine ea eb ++ F) ->
  forall l, l < n -> deg ea eb l = 1%nat -> exists y, In (l, y) F \/ In (y, l) F.
Proof.
  intros n h ea eb F Hv [_ Hs] l Hl Dl.
  destruct Hv as [Vn Vh Va Vb _ _ _]. unfold len in Va, Vb.
  set (m := List.length ea) in *.
  assert (Hm : List.length eb = m) by lia.
  assert (HE : forall p, (p < 2 * m)%nat ->
    nth p (ea ++ eb) 0 = if (p <? m)%nat then nth p ea 0 else nth (p - m) eb 0).
  { intros p Hp. destruct (Nat.ltb_spec p m).
    - apply app_nth1. lia.
    - rewrite app_nth2 by lia. reflexivity. }
  assert (Hlen : List.length (ea ++ eb) = (2 * m)%nat) by (rewrite length_app; lia).
  assert (Il : In l (ea ++ eb)) by (apply count_pos; unfold deg in Dl; lia).
  destruct (In_nth _ _ 0 Il) as (p & Hp & Ep). rewrite Hlen in Hp.
  set (j := if (p <? m)%nat then p else (p - m)%nat).
  assert (Hj : (j < m)%nat) by (unfold j; destruct (Nat.ltb_spec p m); lia).
  (* no other passageway of E has an end at l *)
  assert (Only : forall j', j' <> j -> (j' < m)%nat ->
            nth j' ea 0 = l \/ nth j' eb 0 = l -> False).
  { intros j' Hne Hj' Ej'.
    assert (Q : exists q, (q < 2 * m)%nat /\ q <> p /\ nth q (ea ++ eb) 0 = l).
    { destruct Ej' as [Ej' | Ej'].
      - exists j'. split; [lia|]. split; [unfold j in Hne; destruct (Nat.ltb_spec p m); lia|].
        rewrite HE by lia. destruct (Nat.ltb_spec j' m); [exact Ej' | lia].
      - exists (m + j')%nat. split; [lia|].
        split; [unfold j in Hne; destruct (Nat.ltb_spec p m); lia|].
        rewrite HE by lia. destruct (Nat.ltb_spec (m + j') m); [lia|].
        replace (m + j' - m)%nat with j' by lia. exact Ej'. }
    destruct Q as (q & Hq & Hqp & Eq).
    assert (C : (2 <= count_occ N.eq_dec (ea ++ eb) l)%nat).
    { apply count_two. destruct (Nat.ltb_spec p q).
      - exists p, q. rewrite Hlen. split; [lia|]. auto.
      - exists q, p. rewrite Hlen. split; [lia|]. auto. }
    unfold deg in Dl. lia. }
  assert (HlE : List.length (combine ea eb) = m) by (rewrite length_combine; lia).
  (* a hideout other than l that l must reach once passageway j is blocked *)
  assert (Rt : exists y, y <> l /\ reaches (block (combine ea eb ++ F) j) l y).
  { destruct (N.eq_dec l h) as [-> | Nlh].
    - set (x := if N.eqb h 0 then 1 else 0).
      assert (Hx : x <> h /\ x < n) by (unfold x; destruct (N.eqb_spec h 0); lia).
      exists x. split; [tauto|]. apply reaches_sym. apply Hs; [rewrite length_app; lia | tauto].
    - exists h. split; [auto|]. apply Hs; [rewrite length_app; lia | exact Hl]. }
  destruct Rt as (y & Hyl & [l0 (R1 & R2 & R3 & R4)]).
  destruct l0 as [| a0 l0]; [discriminate|]. simpl in R3. injection R3 as ->.
  destruct l0 as [| z l0]; [simpl in R4; injection R4 as ->; contradiction|].
  simpl in R2. destruct R2 as [J _].
  assert (Nz : z <> l) by (intros ->; inversion R1; subst; simpl in *; tauto).
  rewrite block_app_l in J by lia.
  destruct J as [J | J]; apply in_app_or in J; destruct J as [J | J].
  - destruct (in_block _ _ _ J) as (j' & Hne & Hj' & Ej'). rewrite HlE in Hj'.
    rewrite nth_combine_N in Ej' by lia. injection Ej' as E1 E2.
    exfalso. exact (Only j' Hne Hj' (or_introl E1)).
  - exists z. left. exact J.
  - destruct (in_block _ _ _ J) as (j' & Hne & Hj' & Ej'). rewrite HlE in Hj'.
    rewrite nth_combine_N in Ej' by lia. injection Ej' as E1 E2.
    exfalso. exact (Only j' Hne Hj' (or_intror E2)).
  - exists z. right. exact J.
Qed.

Lemma ends_count : forall (Lv : list N) (F : list (N * N)),
  NoDup Lv -> (forall l, In l Lv -> exists y, In (l, y) F \/ In (y, l) F) ->
  (List.length Lv <= 2 * List.length F)%nat.
Proof.
  intros Lv F Hn Hc.
  assert (Hi : incl Lv (map fst F ++ map snd F)).
  { intros l Hl. destruct (Hc l Hl) as (y & [I | I]); apply in_or_app;
      [left | right]; apply in_map_iff; [exists (l, y) | exists (y, l)]; auto. }
  pose proof (NoDup_incl_length Hn Hi) as H. rewrite length_app, !length_map in H. lia.
Qed.

Section Tree.

Variables (n : N) (m : nat) (ea eb ord : list N) (par : N -> N) (pe : N -> nat) (r : N).

Local Notation D := (deg ea eb).
Local Notation time v := (idx v ord).
Local Notation anc := (anc par r).
Local Notation E := (combine ea eb).

Hypothesis Hea : List.length ea = m.
Hypothesis Heb : List.length eb = m.
Hypothesis Hn : n = N.of_nat m + 1.
Hypothesis Hm1 : (1 <= m)%nat.
Hypothesis Hnd : NoDup ord.
Hypothesis Hall : forall x, In x ord <-> x < n.
Hypothesis Hlen : List.length ord = S m.
Hypothesis Hr : nth 0 ord 0 = r.
Hypothesis Hparr : par r = r.
Hypothesis Hpar : forall v, v < n -> v <> r ->
  (pe v < m)%nat /\ par v < n /\ (time (par v) < time v)%nat /\
  ((nth (pe v) ea 0 = v /\ nth (pe v) eb 0 = par v) \/
   (nth (pe v) ea 0 = par v /\ nth (pe v) eb 0 = v)).
Hypothesis Hchain : forall i, (0 < i < S m)%nat ->
  anc (par (nth i ord 0)) (nth (i - 1) ord 0).

Lemma r_in : In r ord.
Proof. rewrite <- Hr. apply nth_In. lia. Qed.

Lemma r_lt : r < n.
Proof. apply Hall. exact r_in. Qed.

Lemma time_r : time r = 0%nat.
Proof. rewrite <- Hr. apply idx_nth; [exact Hnd | lia]. Qed.

Lemma time_bound : forall x, x < n -> (time x < S m)%nat.
Proof. intros x Hx. rewrite <- Hlen. apply idx_lt. apply Hall. exact Hx. Qed.

Lemma time_inj : forall x y, x < n -> y < n -> time x = time y -> x = y.
Proof. intros x y Hx Hy. apply idx_inj; apply Hall; assumption. Qed.

Lemma time_pos : forall x, x < n -> x <> r -> (0 < time x)%nat.
Proof.
  intros x Hx Hxr. destruct (time x) eqn:E0; [|lia]. exfalso. apply Hxr.
  apply time_inj; [exact Hx | exact r_lt | rewrite E0, time_r; reflexivity].
Qed.

Lemma par_lt : forall x, x < n -> x <> r -> par x < n.
Proof. intros x Hx Hxr. apply (Hpar x Hx Hxr). Qed.

Lemma anc_le : forall a b, anc a b -> b < n -> a < n /\ (time a <= time b)%nat.
Proof.
  intros a b H. induction H as [| y Hy H IH]; intros Hb; [split; [exact Hb | lia]|].
  destruct (Hpar y Hb Hy) as (_ & Hp & Ht & _). destruct (IH Hp). split; [assumption | lia].
Qed.

Lemma anc_lt : forall a b, anc a b -> b < n -> a <> b -> (time a < time b)%nat.
Proof.
  intros a b H Hb Hne. destruct (anc_inv _ _ _ _ H ltac:(auto)) as [Hy H'].
  destruct (Hpar b Hb Hy) as (_ & Hp & Ht & _). destruct (anc_le _ _ H' Hp). lia.
Qed.

Lemma anc_dec : forall a y, y < n -> anc a y \/ ~ anc a y.
Proof.
  intros a y. remember (time y) as t eqn:Et. revert y Et.
  induction t as [t IH] using lt_wf_ind. intros y Et Hy.
  destruct (N.eq_dec y a) as [-> | Nya]; [left; apply anc_refl|].
  destruct (N.eq_dec y r) as [-> | Nyr].
  - right. intros H. destruct (anc_inv _ _ _ _ H Nya). contradiction.
  - destruct (Hpar y Hy Nyr) as (_ & Hp & Ht & _).
    destruct (IH (time (par y)) ltac:(lia) (par y) eq_refl Hp) as [A | NA].
    + left. apply anc_step; assumption.
    + right. intros H. apply NA. exact (proj2 (anc_inv _ _ _ _ H Nya)).
Qed.

Lemma not_anc_root : forall c, c < n -> c <> r -> ~ anc c r.
Proof.
  intros c Hc Hcr H. destruct (anc_le _ _ H r_lt). pose proof (time_pos c Hc Hcr).
  rewrite time_r in *. lia.
Qed.

Lemma he_nth : forall p, (p < 2 * m)%nat ->
  nth p (ea ++ eb) 0 = if (p <? m)%nat then nth p ea 0 else nth (p - m) eb 0.
Proof.
  intros p Hp. destruct (Nat.ltb_spec p m).
  - apply app_nth1. lia.
  - rewrite app_nth2 by lia. rewrite Hea. reflexivity.
Qed.

Lemma pe_inj : forall v w, v < n -> v <> r -> w < n -> w <> r -> pe v = pe w -> v = w.
Proof.
  intros v w Hv Hvr Hw Hwr E0.
  destruct (Hpar v Hv Hvr) as (_ & Hpv & Htv & [[A1 A2] | [A1 A2]]);
  destruct (Hpar w Hw Hwr) as (_ & Hpw & Htw & [[B1 B2] | [B1 B2]]);
  rewrite E0 in A1, A2; try congruence.
  - assert (P1 : par w = v) by congruence. assert (P2 : par v = w) by congruence.
    rewrite P1 in Htw. rewrite P2 in Htv. lia.
  - assert (P1 : par w = v) by congruence. assert (P2 : par v = w) by congruence.
    rewrite P1 in Htw. rewrite P2 in Htv. lia.
Qed.

Lemma pe_surj : forall j, (j < m)%nat -> exists v, v < n /\ v <> r /\ pe v = j.
Proof.
  intros j Hj. pose proof (list_hd_tl ord m Hlen) as Eo. rewrite Hr in Eo.
  set (t := tl ord) in *.
  assert (Ht : forall x, In x t -> x < n /\ x <> r).
  { intros x Hx. split; [apply Hall; rewrite Eo; right; exact Hx|].
    intros ->. rewrite Eo in Hnd. inversion Hnd; contradiction. }
  assert (Hnt : NoDup t) by (rewrite Eo in Hnd; inversion Hnd; assumption).
  assert (Hlt : List.length t = m) by (rewrite Eo in Hlen; simpl in Hlen; lia).
  assert (Hin : In j (map pe t)).
  { apply (pigeon _ m); [| rewrite length_map; exact Hlt | | exact Hj].
    - apply nodup_map_inj; [exact Hnt|]. intros x y Hx Hy.
      destruct (Ht x Hx), (Ht y Hy). apply pe_inj; assumption.
    - intros x Hx. apply in_map_iff in Hx. destruct Hx as (y & <- & Hy).
      destruct (Ht y Hy). apply (Hpar y); assumption. }
  apply in_map_iff in Hin. destruct Hin as (v & Ev & Hv). destruct (Ht v Hv).
  exists v. auto.
Qed.

Lemma inc_cases : forall j x, (j < m)%nat -> endp ea eb j x ->
  exists y, y < n /\ y <> r /\ pe y = j /\ (x = y \/ x = par y).
Proof.
  intros j x Hj Hx. destruct (pe_surj j Hj) as (y & Hy & Hyr & <-).
  exists y. split; [exact Hy|]. split; [exact Hyr|]. split; [reflexivity|].
  destruct (Hpar y Hy Hyr) as (_ & _ & _ & [[A1 A2] | [A1 A2]]);
    destruct Hx as [Hx | Hx]; rewrite Hx in *; auto.
Qed.

Lemma pos_edge : forall p x, (p < 2 * m)%nat -> nth p (ea ++ eb) 0 = x ->
  exists j, (j < m)%nat /\ endp ea eb j x /\ (p = j \/ p = m + j)%nat.
Proof.
  intros p x Hp Ex. rewrite he_nth in Ex by exact Hp. destruct (Nat.ltb_spec p m).
  - exists p. split; [lia|]. split; [left; exact Ex | left; reflexivity].
  - exists (p - m)%nat. split; [lia|]. split; [right; exact Ex | right; lia].
Qed.

Lemma edge_pos : forall j x, (j < m)%nat -> endp ea eb j x ->
  In x (ea ++ eb).
Proof.
  intros j x Hj [H | H]; apply in_or_app; [left | right]; rewrite <- H; apply nth_In; lia.
Qed.

Lemma he_len : List.length (ea ++ eb) = (2 * m)%nat.
Proof. rewrite length_app. lia. Qed.

Lemma pe_endp : forall v, v < n -> v <> r -> endp ea eb (pe v) v.
Proof.
  intros v Hv Hvr. destruct (Hpar v Hv Hvr) as (_ & _ & _ & [[A1 A2] | [A1 A2]]);
    [left | right]; assumption.
Qed.

Lemma par_endp : forall v, v < n -> v <> r -> endp ea eb (pe v) (par v).
Proof.
  intros v Hv Hvr. destruct (Hpar v Hv Hvr) as (_ & _ & _ & [[A1 A2] | [A1 A2]]);
    [right | left]; assumption.
Qed.

(* two ends at x on distinct positions come from distinct passageways,
   unless passageway j joins x to itself *)
Lemma loop_free : forall j, (j < m)%nat -> nth j ea 0 = nth j eb 0 -> False.
Proof.
  intros j Hj E0. destruct (pe_surj j Hj) as (y & Hy & Hyr & <-).
  destruct (Hpar y Hy Hyr) as (_ & _ & Ht & [[A1 A2] | [A1 A2]]);
    assert (Py : par y = y) by congruence; rewrite Py in Ht; lia.
Qed.

Lemma two_ends : forall p p' x, (p < p' < 2 * m)%nat ->
  nth p (ea ++ eb) 0 = x -> nth p' (ea ++ eb) 0 = x ->
  exists j j', (j < m)%nat /\ (j' < m)%nat /\ j <> j' /\ endp ea eb j x /\ endp ea eb j' x.
Proof.
  intros p p' x Hp Ex Ex'.
  destruct (pos_edge p x ltac:(lia) Ex) as (j & Hj & Ej & Pj).
  destruct (pos_edge p' x ltac:(lia) Ex') as (j' & Hj' & Ej' & Pj').
  exists j, j'. split; [exact Hj|]. split; [exact Hj'|]. split; [|auto].
  intros <-. rewrite he_nth in Ex, Ex' by lia.
  destruct Pj as [-> | ->]; destruct Pj' as [-> | ->]; try lia.
  destruct (Nat.ltb_spec j m); [|lia]. destruct (Nat.ltb_spec (m + j) m); [lia|].
  replace (m + j - m)%nat with j in Ex' by lia. apply (loop_free j Hj). congruence.
Qed.

Lemma childless_leaf : forall x, x < n -> x <> r ->
  (forall y, y < n -> y <> r -> par y <> x) -> D x = 1%nat.
Proof.
  intros x Hx Hxr Hc. unfold deg.
  assert (H1 : (1 <= count_occ N.eq_dec (ea ++ eb) x)%nat).
  { apply count_pos. apply (edge_pos (pe x)); [apply (Hpar x Hx Hxr) | apply pe_endp; assumption]. }
  destruct (Nat.le_gt_cases 2 (count_occ N.eq_dec (ea ++ eb) x)) as [H2 | H2]; [|lia].
  exfalso. apply count_two in H2. destruct H2 as (p & p' & Hp & Ep & Ep').
  rewrite he_len in Hp.
  destruct (two_ends p p' x Hp Ep Ep') as (j & j' & Hj & Hj' & Hne & Ej & Ej').
  destruct (inc_cases j x Hj Ej) as (y & Hy & Hyr & Py & [<- | Ey]);
    [| exact (Hc y Hy Hyr (eq_sym Ey))].
  destruct (inc_cases j' x Hj' Ej') as (y' & Hy' & Hyr' & Py' & [E2 | Ey']);
    [congruence | exact (Hc y' Hy' Hyr' (eq_sym Ey'))].
Qed.

Lemma sub_leaf : forall c, c < n -> c <> r ->
  exists l, l < n /\ l <> r /\ anc c l /\ D l = 1%nat.
Proof.
  intros c Hc Hcr.
  assert (G : forall k x, (S m - time x <= k)%nat -> x < n -> x <> r -> anc c x ->
            exists l, l < n /\ l <> r /\ anc c l /\ D l = 1%nat).
  { induction k as [| k IH]; intros x Hk Hx Hxr Ha.
    - pose proof (time_bound x Hx). lia.
    - destruct (existsb (fun y => (negb (N.eqb y r) && N.eqb (par y) x)%bool) ord) eqn:Eb.
      + apply existsb_exists in Eb. destruct Eb as (y & Hy & Ey).
        apply andb_prop in Ey. destruct Ey as [Ey1 Ey2].
        apply Bool.negb_true_iff, N.eqb_neq in Ey1. apply N.eqb_eq in Ey2.
        apply Hall in Hy. destruct (Hpar y Hy Ey1) as (_ & _ & Ht & _).
        rewrite Ey2 in Ht. pose proof (time_bound y Hy).
        apply (IH y); [lia | exact Hy | exact Ey1 |].
        apply anc_step; [exact Ey1 | rewrite Ey2; exact Ha].
      + exists x. split; [exact Hx|]. split; [exact Hxr|]. split; [exact Ha|].
        apply childless_leaf; [exact Hx | exact Hxr|]. intros y Hy Hyr Ey.
        assert (Hin : In y ord) by (apply Hall; exact Hy).
        assert (existsb (fun y => (negb (N.eqb y r) && N.eqb (par y) x)%bool) ord = true).
        { apply existsb_exists. exists y. split; [exact Hin|].
          rewrite Ey, N.eqb_refl. destruct (N.eqb_spec y r); [contradiction | reflexivity]. }
        congruence. }
  apply (G (S m) c); [lia | exact Hc | exact Hcr | apply anc_refl].
Qed.

Lemma root_child : exists y, y < n /\ y <> r /\ par y = r.
Proof.
  set (y := nth 1 ord 0).
  assert (Hy : y < n) by (apply Hall; apply nth_In; lia).
  assert (Hyr : y <> r).
  { intros E0. assert (idx y ord = 1%nat) by (apply idx_nth; [exact Hnd | lia]).
    rewrite E0, time_r in H. discriminate. }
  exists y. split; [exact Hy|]. split; [exact Hyr|].
  destruct (Hpar y Hy Hyr) as (_ & Hp & Ht & _).
  assert (idx y ord = 1%nat) by (apply idx_nth; [exact Hnd | lia]).
  apply time_inj; [exact Hp | exact r_lt | rewrite time_r; lia].
Qed.

Lemma leaf_out : forall c, c < n -> c <> r ->
  exists l, l < n /\ D l = 1%nat /\ ~ anc c l.
Proof.
  intros c Hc Hcr.
  destruct (Nat.eq_dec (D r) 1) as [Dr | Dr].
  - exists r. split; [exact r_lt|]. split; [exact Dr|]. apply not_anc_root; assumption.
  - assert (H1 : (1 <= D r)%nat).
    { destruct root_child as (y & Hy & Hyr & Py). unfold deg. apply count_pos.
      apply (edge_pos (pe y)); [apply (Hpar y Hy Hyr)|]. rewrite <- Py.
      apply par_endp; assumption. }
    assert (H2 : (2 <= count_occ N.eq_dec (ea ++ eb) r)%nat) by (unfold deg in *; lia).
    apply count_two in H2. destruct H2 as (p & p' & Hp & Ep & Ep').
    rewrite he_len in Hp.
    destruct (two_ends p p' r Hp Ep Ep') as (j & j' & Hj & Hj' & Hne & Ej & Ej').
    destruct (inc_cases j r Hj Ej) as (y & Hy & Hyr & Py & [E1 | Ey]); [congruence|].
    destruct (inc_cases j' r Hj' Ej') as (y' & Hy' & Hyr' & Py' & [E1 | Ey']); [congruence|].
    assert (Hyy : y <> y') by (intros <-; congruence).
    assert (Hz : exists z, z < n /\ z <> r /\ par z = r /\ ~ anc z c).
    { destruct (anc_dec y c Hc) as [A | NA]; [| exists y; auto].
      destruct (anc_dec y' c Hc) as [A' | NA']; [| exists y'; auto].
      exfalso. destruct (anc_total _ _ _ _ _ A A') as [B | B].
      - destruct (anc_inv _ _ _ _ B (not_eq_sym Hyy)) as [_ B'].
        rewrite <- Ey' in B'. exact (not_anc_root y Hy Hyr B').
      - destruct (anc_inv _ _ _ _ B Hyy) as [_ B'].
        rewrite <- Ey in B'. exact (not_anc_root y' Hy' Hyr' B'). }
    destruct Hz as (z & Hz & Hzr & Pz & NA).
    destruct (sub_leaf z Hz Hzr) as (l & Hl & Hlr & Al & Dl).
    exists l. split; [exact Hl|]. split; [exact Dl|]. intros Acl.
    destruct (anc_total _ _ _ _ _ Acl Al) as [B | B]; [| exact (NA B)].
    destruct (N.eq_dec z c) as [-> | Nzc]; [exact (NA (anc_refl _ _ _))|].
    destruct (anc_inv _ _ _ _ B Nzc) as [_ B']. rewrite Pz in B'.
    exact (not_anc_root c Hc Hcr B').
Qed.

Lemma contig_step : forall c i, c < n -> (time c < i < S m)%nat ->
  anc c (nth i ord 0) -> anc c (nth (i - 1) ord 0).
Proof.
  intros c i Hc Hi Ha.
  assert (Ne : nth i ord 0 <> c).
  { intros E0. assert (idx (nth i ord 0) ord = i) by (apply idx_nth; [exact Hnd | lia]).
    rewrite E0 in H. lia. }
  destruct (anc_inv _ _ _ _ Ha Ne) as [_ Ha'].
  apply (anc_trans _ _ _ _ _ Ha'). apply Hchain. lia.
Qed.

Lemma contig : forall c i, c < n -> (i < S m)%nat -> (time c <= i)%nat ->
  anc c (nth i ord 0) -> forall j, (time c <= j <= i)%nat -> anc c (nth j ord 0).
Proof.
  intros c i Hc. induction i as [| i IH]; intros Hi Hti Ha j Hj.
  - replace j with 0%nat by lia. exact Ha.
  - destruct (Nat.eq_dec j (S i)) as [-> | Ne]; [exact Ha|].
    apply IH; [lia | lia | | lia].
    replace i with (S i - 1)%nat by lia. apply contig_step; [exact Hc | lia | exact Ha].
Qed.

Lemma lenE : List.length E = m.
Proof. rewrite length_combine. lia. Qed.

Lemma edge_join : forall k v, v < n -> v <> r -> pe v <> k ->
  joined (block E k) v (par v).
Proof.
  intros k v Hv Hvr Hk.
  destruct (Hpar v Hv Hvr) as (Hpe & _ & _ & Hor).
  pose proof (block_in E k (pe v) Hk ltac:(rewrite lenE; exact Hpe)) as B.
  rewrite nth_combine_N in B by lia.
  destruct Hor as [[A1 A2] | [A1 A2]]; rewrite A1, A2 in B; [left | right]; exact B.
Qed.

Lemma reach_out : forall c0, c0 < n -> c0 <> r ->
  forall x, x < n -> ~ anc c0 x -> reaches (block E (pe c0)) x r.
Proof.
  intros c0 Hc Hcr x. remember (time x) as t eqn:Et. revert x Et.
  induction t as [t IH] using lt_wf_ind. intros x Et Hx Na.
  destruct (N.eq_dec x r) as [-> | Nxr]; [apply reaches_refl|].
  destruct (Hpar x Hx Nxr) as (_ & Hp & Ht & _).
  assert (Nxc : x <> c0) by (intros ->; exact (Na (anc_refl _ _ _))).
  apply reaches_trans with (par x).
  - apply joined_reaches. apply edge_join; [exact Hx | exact Nxr|].
    intro E0. exact (Nxc (pe_inj x c0 Hx Nxr Hc Hcr E0)).
  - apply (IH (time (par x))); [lia | reflexivity | exact Hp|].
    intro A. apply Na. apply anc_step; assumption.
Qed.

Lemma reach_in : forall c0, c0 < n -> c0 <> r ->
  forall x, x < n -> anc c0 x -> reaches (block E (pe c0)) x c0.
Proof.
  intros c0 Hc Hcr x. remember (time x) as t eqn:Et. revert x Et.
  induction t as [t IH] using lt_wf_ind. intros x Et Hx A.
  destruct (N.eq_dec x c0) as [-> | Nxc]; [apply reaches_refl|].
  destruct (anc_inv _ _ _ _ A Nxc) as [Nxr A'].
  destruct (Hpar x Hx Nxr) as (_ & Hp & Ht & _).
  apply reaches_trans with (par x).
  - apply joined_reaches. apply edge_join; [exact Hx | exact Nxr|].
    intro E0. exact (Nxc (pe_inj x c0 Hx Nxr Hc Hcr E0)).
  - apply (IH (time (par x))); [lia | reflexivity | exact Hp | exact A'].
Qed.

(* the leaves in visiting order *)
Definition leaves : list N := filter (fun v => Nat.eqb (D v) 1) ord.

Lemma leaves_in : forall l, In l leaves <-> l < n /\ D l = 1%nat.
Proof.
  intros l. unfold leaves. rewrite filter_In, Hall, Nat.eqb_eq. reflexivity.
Qed.

Lemma leaves_nodup : NoDup leaves.
Proof. apply NoDup_filter. exact Hnd. Qed.

Lemma leaves_conv : forall c, c < n -> forall i j k,
  (i < j < k)%nat -> (k < List.length leaves)%nat ->
  anc c (nth i leaves 0) -> anc c (nth k leaves 0) -> anc c (nth j leaves 0).
Proof.
  intros c Hc i j k Hijk Hk Ai Ak.
  assert (Hin : forall q, (q < List.length leaves)%nat -> nth q leaves 0 < n).
  { intros q Hq. apply (proj1 (leaves_in _)). apply nth_In. exact Hq. }
  pose proof (filter_order (fun v => Nat.eqb (D v) 1) ord i j Hnd ltac:(fold leaves; lia)) as O1.
  pose proof (filter_order (fun v => Nat.eqb (D v) 1) ord j k Hnd ltac:(fold leaves; lia)) as O2.
  fold leaves in O1, O2.
  destruct (anc_le _ _ Ai (Hin i ltac:(lia))) as [_ Li].
  pose proof (time_bound _ (Hin k Hk)) as Bk.
  rewrite <- (nth_idx (nth j leaves 0) ord 0) by (apply Hall; apply Hin; lia).
  apply (contig c (time (nth k leaves 0))); [exact Hc | exact Bk | lia | | lia].
  rewrite nth_idx by (apply Hall; apply Hin; exact Hk). exact Ak.
Qed.

Section Pairing.

Local Notation L := (List.length leaves).
Local Notation a := (L / 2)%nat.
Local Notation xs := (firstn (L - a) leaves).
Local Notation ys := (skipn a leaves).

Lemma pair_in : forall i, (i < L - a)%nat ->
  In (nth i leaves 0, nth (i + a) leaves 0) (combine xs ys).
Proof.
  intros i Hi.
  assert (Lx : List.length xs = (L - a)%nat) by (rewrite length_firstn; lia).
  assert (Ly : List.length ys = (L - a)%nat) by (rewrite length_skipn; lia).
  replace (nth i leaves 0, nth (i + a) leaves 0) with (nth i (combine xs ys) (0, 0)).
  - apply nth_In. rewrite length_combine. lia.
  - rewrite nth_combine_N by lia. rewrite nth_firstn, nth_skipn.
    destruct (Nat.ltb_spec i (L - a)); [|lia]. f_equal. f_equal. lia.
Qed.

Lemma cross_edge : forall c0, c0 < n -> c0 <> r ->
  reaches (block E (pe c0) ++ combine xs ys) c0 (par c0).
Proof.
  intros c0 Hc Hcr.
  set (G := block E (pe c0) ++ combine xs ys).
  assert (Mono : incl (block E (pe c0)) G) by (intros p Hp; apply in_or_app; left; exact Hp).
  assert (Hin : forall q, (q < L)%nat -> nth q leaves 0 < n).
  { intros q Hq. apply (proj1 (leaves_in _)). apply nth_In. exact Hq. }
  destruct (Hpar c0 Hc Hcr) as (_ & Hp & Ht & _).
  assert (Npc : ~ anc c0 (par c0)).
  { intros A. destruct (anc_le _ _ A Hp). lia. }
  assert (Out : forall x, x < n -> ~ anc c0 x -> reaches G x (par c0)).
  { intros x Hx Nx. apply (reaches_mono (block E (pe c0))); [exact Mono|].
    apply reaches_trans with r; [apply reach_out; assumption|].
    apply reaches_sym. apply reach_out; assumption. }
  assert (In0 : forall x, x < n -> anc c0 x -> reaches G c0 x).
  { intros x Hx Ax. apply (reaches_mono (block E (pe c0))); [exact Mono|].
    apply reaches_sym. apply reach_in; assumption. }
  destruct (cross (fun i => anc c0 (nth i leaves 0)) L) as (i & Hi & Hx).
  - intros i Hi. apply anc_dec. apply Hin. exact Hi.
  - intros i j k Hijk Hk. apply leaves_conv; assumption.
  - destruct (sub_leaf c0 Hc Hcr) as (l & Hl & _ & Al & Dl).
    assert (Il : In l leaves) by (apply leaves_in; auto).
    exists (idx l leaves). split; [apply idx_lt; exact Il|].
    rewrite nth_idx by exact Il. exact Al.
  - destruct (leaf_out c0 Hc Hcr) as (l & Hl & Dl & Nl).
    assert (Il : In l leaves) by (apply leaves_in; auto).
    exists (idx l leaves). split; [apply idx_lt; exact Il|].
    rewrite nth_idx by exact Il. exact Nl.
  - pose proof (pair_in i Hi) as Pi.
    assert (J : reaches G (nth i leaves 0) (nth (i + a) leaves 0)).
    { apply joined_reaches. left. apply in_or_app. right. exact Pi. }
    destruct Hx as [[A NA] | [NA A]].
    + apply reaches_trans with (nth i leaves 0); [apply In0; [apply Hin; lia | exact A]|].
      apply reaches_trans with (nth (i + a) leaves 0); [exact J|].
      apply Out; [apply Hin; lia | exact NA].
    + apply reaches_trans with (nth (i + a) leaves 0); [apply In0; [apply Hin; lia | exact A]|].
      apply reaches_trans with (nth i leaves 0); [apply reaches_sym; exact J|].
      apply Out; [apply Hin; lia | exact NA].
Qed.

Lemma tree_spec : forall h, valid_input n h ea eb ->
  kingpin_escape_spec n h ea eb (firstn (L - a) leaves, skipn a leaves).
Proof.
  intros h Hv. pose proof Hv as Hv'.
  destruct Hv' as [Vn Vh Va Vb VA VB Vt].
  unfold kingpin_escape_spec, safe, in_range, passageways in *.
  assert (Lx : List.length (firstn (L - a) leaves) = (L - a)%nat) by (rewrite length_firstn; lia).
  assert (Ly : List.length (skipn a leaves) = (L - a)%nat) by (rewrite length_skipn; lia).
  assert (Tr : forall x, x < n -> reaches E x h).
  { intros x Hx. destruct (Vt x h Hx Vh) as (l & Hl & _). exists l. exact Hl. }
  assert (Ea : forall a0 b0, In (a0, b0) (combine xs ys) -> In a0 leaves /\ In b0 leaves).
  { intros a0 b0 I. split.
    - apply in_combine_l in I. rewrite <- (firstn_skipn (L - a) leaves).
      apply in_or_app. left. exact I.
    - apply in_combine_r in I. rewrite <- (firstn_skipn a leaves).
      apply in_or_app. right. exact I. }
  split; [unfold len; rewrite Lx, Ly; reflexivity|].
  split; [|split].
  - intros a0 b0 I. destruct (Ea a0 b0 I) as [I1 I2].
    apply leaves_in in I1, I2. tauto.
  - split.
    + intros x Hx. apply (reaches_mono E); [intros p Hp; apply in_or_app; left; exact Hp|].
      apply Tr. exact Hx.
    + intros k x Hk Hx. rewrite length_app, lenE in Hk.
      destruct (Nat.ltb_spec k m) as [Hkm | Hkm].
      * rewrite block_app_l by (rewrite lenE; exact Hkm).
        destruct (pe_surj k Hkm) as (c0 & Hc & Hcr & <-).
        apply (reaches_bridge E); [| apply Tr; exact Hx].
        intros a0 b0 I. destruct (In_nth _ _ (0, 0) I) as (j & Hj & Ej).
        rewrite lenE in Hj.
        destruct (Nat.eq_dec j (pe c0)) as [-> | Ne].
        -- rewrite nth_combine_N in Ej by lia. injection Ej as E1 E2.
           pose proof (cross_edge c0 Hc Hcr) as C.
           destruct (Hpar c0 Hc Hcr) as (_ & _ & _ & [[A1 A2] | [A1 A2]]).
           ++ rewrite <- E1, <- E2, A1, A2. exact C.
           ++ rewrite <- E1, <- E2, A1, A2. apply reaches_sym. exact C.
        -- apply joined_reaches. left. apply in_or_app. left. rewrite <- Ej.
           apply block_in; [exact Ne | rewrite lenE; exact Hj].
      * apply (reaches_mono E); [apply block_app_r; rewrite lenE; exact Hkm|].
        apply Tr. exact Hx.
  - intros F HF Hs. unfold len. rewrite Lx.
    assert (C : (L <= 2 * List.length F)%nat).
    { apply ends_count; [exact leaves_nodup|]. intros l Il. apply leaves_in in Il.
      destruct Il as [Il Dl]. exact (leaf_needs n h ea eb F Hv Hs l Il Dl). }
    pose proof (Nat.div_mod L 2 ltac:(lia)). pose proof (Nat.mod_upper_bound L 2 ltac:(lia)).
    lia.
Qed.

End Pairing.

End Tree.

(* ------------------------------------------------------------------ *)
(* The loops                                                           *)
(* ------------------------------------------------------------------ *)

Open Scope uint63_scope.

Lemma cnt_loop_eq : forall col m i deg H,
  cnt_loop col m i deg H =
  match bdec (i <? m) with
  | left Hi =>
      let v := col.[i] in
      cnt_loop col m (i + 1) deg.[v <- deg.[v] + 1] (Acc_inv H (dec_step m i Hi))
  | right _ => deg
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma pre_loop_eq : forall deg n i acc pos H,
  pre_loop deg n i acc pos H =
  match bdec (i <? n) with
  | left Hi =>
      pre_loop deg n (i + 1) (acc + deg.[i]) pos.[i <- acc]
        (Acc_inv H (dec_step n i Hi))
  | right _ => pos
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma fill_loop_eq : forall col base m i pos adj H,
  fill_loop col base m i pos adj H =
  match bdec (i <? m) with
  | left Hi =>
      let v := col.[i] in
      let p := pos.[v] in
      fill_loop col base m (i + 1) pos.[v <- p + 1] adj.[p <- base + i]
        (Acc_inv H (dec_step m i Hi))
  | right _ => (pos, adj)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma nb_loop_eq : forall ea eb adj m e s mark stk sp H,
  nb_loop ea eb adj m e s mark stk sp H =
  match bdec (s <? e) with
  | left Hs =>
      let w := other ea eb m adj.[s] in
      if mark.[w] =? 0 then
        nb_loop ea eb adj m e (s + 1) mark.[w <- 1] stk.[sp <- w] (sp + 1)
          (Acc_inv H (dec_step e s Hs))
      else
        nb_loop ea eb adj m e (s + 1) mark stk sp
          (Acc_inv H (dec_step e s Hs))
  | right _ => (mark, stk, sp)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma dfs_loop_eq : forall ea eb adj deg pos n m t mark stk sp lv L H,
  dfs_loop ea eb adj deg pos n m t mark stk sp lv L H =
  match bdec (t <? n) with
  | left Ht =>
      if 0 <? sp then
        let v := stk.[sp - 1] in
        let dv := deg.[v] in
        let e := pos.[v] in
        let lv' := if dv =? 1 then lv.[L <- v] else lv in
        let L' := if dv =? 1 then L + 1 else L in
        match nb_loop ea eb adj m e (e - dv) mark stk (sp - 1)
                (Zwf_well_founded 0 (gap e (e - dv))) with
        | (mark', stk', sp') =>
            dfs_loop ea eb adj deg pos n m (t + 1) mark' stk' sp' lv' L'
              (Acc_inv H (dec_step n t Ht))
        end
      else (lv, L)
  | right _ => (lv, L)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma root_loop_eq : forall deg n i H,
  root_loop deg n i H =
  match bdec (i <? n) with
  | left Hi =>
      if 2 <=? deg.[i] then i
      else root_loop deg n (i + 1) (Acc_inv H (dec_step n i Hi))
  | right _ => 0%uint63
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma out_loop_eq : forall lv a c i xs ys H,
  out_loop lv a c i xs ys H =
  match bdec (i <? c) with
  | left Hi =>
      out_loop lv a c (i + 1) xs.[i <- lv.[i]] ys.[i <- lv.[i + a]]
        (Acc_inv H (dec_step c i Hi))
  | right _ => (xs, ys)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Open Scope N_scope.

Lemma ltb_true : forall x y, (x <? y)%uint63 = true -> nv x < nv y.
Proof. intros x y H. rewrite ltb_nv in H. apply N.ltb_lt. exact H. Qed.

Lemma ltb_false : forall x y, (x <? y)%uint63 = false -> nv y <= nv x.
Proof. intros x y H. rewrite ltb_nv in H. apply N.ltb_ge. exact H. Qed.

Lemma firstn_snoc : forall (l : list N) i, (i < List.length l)%nat ->
  firstn (S i) l = firstn i l ++ [nth i l 0].
Proof.
  intros l. induction l as [| x l IH]; intros i Hi; simpl in Hi; [lia|].
  destruct i as [| i]; [reflexivity|].
  change (firstn (S (S i)) (x :: l)) with (x :: firstn (S i) l).
  rewrite IH by lia. reflexivity.
Qed.

Lemma count_snoc : forall (l : list N) i w, (i < List.length l)%nat ->
  count_occ N.eq_dec (firstn (S i) l) w =
  (count_occ N.eq_dec (firstn i l) w + if N.eq_dec (nth i l 0%N) w then 1 else 0)%nat.
Proof.
  intros l i w Hi. rewrite firstn_snoc by exact Hi. rewrite count_occ_app. simpl.
  destruct (N.eq_dec (nth i l 0) w); reflexivity.
Qed.

Lemma count_firstn_le : forall (l : list N) k w,
  (count_occ N.eq_dec (firstn k l) w <= count_occ N.eq_dec l w)%nat.
Proof.
  intros l k w. rewrite <- (firstn_skipn k l) at 2. rewrite count_occ_app. lia.
Qed.

Lemma arr_get : forall a l i, arr_is a l -> nv i < N.of_nat (List.length l) ->
  nv a.[i] = nth (N.to_nat (nv i)) l 0.
Proof.
  intros a l i [_ Hc] Hi. rewrite <- rd_nv. rewrite <- (N2Nat.id (nv i)) at 1.
  apply Hc. lia.
Qed.

Lemma forall_nth_lt : forall (l : list N) n k, Forall (fun x => x < n) l ->
  (k < List.length l)%nat -> nth k l 0 < n.
Proof.
  intros l n k H Hk. rewrite Forall_forall in H. apply H. apply nth_In. exact Hk.
Qed.

(* csum l k: the number of elements of l below k *)
Fixpoint csum (l : list N) (k : nat) : nat :=
  match k with
  | O => O
  | S k => (csum l k + count_occ N.eq_dec l (N.of_nat k))%nat
  end.

Lemma csum_mono : forall l k k', (k <= k')%nat -> (csum l k <= csum l k')%nat.
Proof.
  intros l k k' H. induction H as [| k' H IH]; [lia|]. simpl. lia.
Qed.

Lemma csum_disj : forall l v w, (v < w)%nat ->
  (csum l v + count_occ N.eq_dec l (N.of_nat v) <= csum l w)%nat.
Proof.
  intros l v w H. change (csum l v + count_occ N.eq_dec l (N.of_nat v))%nat with (csum l (S v)).
  apply csum_mono. lia.
Qed.

Lemma csum_cons : forall x l k,
  csum (x :: l) k = (csum l k + if (N.to_nat x <? k)%nat then 1 else 0)%nat.
Proof.
  intros x l k. induction k as [| k IH]; [reflexivity|].
  simpl csum. rewrite IH. simpl count_occ.
  destruct (N.eq_dec x (N.of_nat k)) as [E | E];
    destruct (Nat.ltb_spec (N.to_nat x) k); destruct (Nat.ltb_spec (N.to_nat x) (S k)); lia.
Qed.

Lemma csum_total : forall l n, Forall (fun x => x < n) l -> csum l (N.to_nat n) = List.length l.
Proof.
  intros l n H. induction l as [| x l IH]; simpl.
  - induction (N.to_nat n) as [| k IHk]; simpl; [reflexivity | rewrite IHk; reflexivity].
  - inversion H as [| ? ? Hx Hl]; subst. rewrite csum_cons, IH by exact Hl.
    destruct (Nat.ltb_spec (N.to_nat x) (N.to_nat n)); lia.
Qed.

Section Machine.

Variables (n : N) (m : nat) (ea eb : list N) (eaA ebA : array int) (mI : int).

Hypothesis Hea : List.length ea = m.
Hypothesis Heb : List.length eb = m.
Hypothesis Hn : n = N.of_nat m + 1.
Hypothesis Hnb : n <= 100000.
Hypothesis HeaA : arr_is eaA ea.
Hypothesis HebA : arr_is ebA eb.
Hypothesis HVa : Forall (fun x => x < n) ea.
Hypothesis HVb : Forall (fun x => x < n) eb.
Hypothesis HmI : nv mI = N.of_nat m.

Local Notation HE := (ea ++ eb).
Local Notation D := (deg ea eb).

Lemma cnt_spec : forall col cl (base : N -> N),
  arr_is col cl -> List.length cl = m -> Forall (fun x => x < n) cl ->
  (forall v, v < n -> base v + N.of_nat (count_occ N.eq_dec cl v) < 4611686018427387904) ->
  forall z i deg H, gap mI i = z -> nv i <= N.of_nat m -> nv (PArray.length deg) = n ->
  (forall v, v < n -> rd deg v =
     base v + N.of_nat (count_occ N.eq_dec (firstn (N.to_nat (nv i)) cl) v)) ->
  nv (PArray.length (cnt_loop col mI i deg H)) = n /\
  forall v, v < n -> rd (cnt_loop col mI i deg H) v =
     base v + N.of_nat (count_occ N.eq_dec cl v).
Proof.
  intros col cl base Hc Hl Hf Hb z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i deg H Hz Hi Hd Hinv.
  rewrite cnt_loop_eq. destruct (bdec (i <? mI)%uint63) as [Hlt | Hge].
  - pose proof (ltb_true _ _ Hlt) as Hlt'.
    cbv zeta.
    assert (Ex : nv col.[i] = nth (N.to_nat (nv i)) cl 0) by (apply arr_get; [exact Hc | lia]).
    assert (Bx : nv col.[i] < n) by (rewrite Ex; apply forall_nth_lt; [exact Hf | lia]).
    pose proof (nv_lt i).
    assert (Hi1 : nv (i + 1)%uint63 = nv i + 1) by (apply nv_add_N; rewrite nv_1; lia).
    eapply IH; [ | reflexivity | | | ].
    + rewrite <- Hz. apply dec_step. exact Hlt.
    + lia.
    + rewrite alength_set. exact Hd.
    + intros v Hv. rewrite Hi1, N2Nat.inj_add, Nat.add_1_r, count_snoc by lia.
      rewrite <- Ex.
      destruct (N.eq_dec (nv col.[i]) v) as [<- | Ne].
      * rewrite rd_set_same by (reflexivity || lia).
        specialize (Hb (nv col.[i]) Bx).
        pose proof (count_firstn_le cl (N.to_nat (nv i)) (nv col.[i])).
        rewrite nv_add_N; rewrite nv_1, <- rd_nv, Hinv by exact Bx; lia.
      * rewrite rd_set_other by lia. rewrite Hinv by exact Hv. lia.
  - pose proof (ltb_false _ _ Hge).
    split; [exact Hd|]. intros v Hv. rewrite Hinv by exact Hv.
    rewrite firstn_all2 by lia. reflexivity.
Qed.

(* the first slot of v in the adjacency *)
Definition ofs (v : N) : N := N.of_nat (csum HE (N.to_nat v)).

Lemma HE_lt : forall p, (p < 2 * m)%nat -> nth p HE 0 < n.
Proof.
  intros p Hp. apply forall_nth_lt; [apply Forall_app; auto | rewrite length_app; lia].
Qed.

Lemma ofs_D : forall v, ofs v + N.of_nat (D v) = N.of_nat (csum HE (S (N.to_nat v))).
Proof. intros v. unfold ofs, deg. simpl. rewrite N2Nat.id. lia. Qed.

Lemma ofs_end : forall v, v < n -> ofs v + N.of_nat (D v) <= N.of_nat (2 * m).
Proof.
  intros v Hv. rewrite ofs_D.
  assert (T : csum HE (N.to_nat n) = (2 * m)%nat).
  { rewrite csum_total with (n := n); [rewrite length_app; lia | apply Forall_app; auto]. }
  pose proof (csum_mono HE (S (N.to_nat v)) (N.to_nat n) ltac:(lia)). lia.
Qed.

Lemma ofs_disj : forall v w s, v < n -> w < n ->
  ofs v <= s < ofs v + N.of_nat (D v) -> ofs w <= s < ofs w + N.of_nat (D w) -> v = w.
Proof.
  intros v w s Hv Hw H1 H2. unfold ofs, deg in *.
  destruct (N.lt_trichotomy v w) as [L | [E | L]]; [| exact E |].
  - pose proof (csum_disj HE (N.to_nat v) (N.to_nat w) ltac:(lia)). rewrite N2Nat.id in H. lia.
  - pose proof (csum_disj HE (N.to_nat w) (N.to_nat v) ltac:(lia)). rewrite N2Nat.id in H. lia.
Qed.

Lemma pre_spec : forall degA nI, nv nI = n ->
  (forall v, v < n -> rd degA v = N.of_nat (D v)) ->
  forall z i acc pos H, gap nI i = z -> nv i <= n -> nv acc = ofs (nv i) ->
  nv (PArray.length pos) = n -> (forall v, v < nv i -> rd pos v = ofs v) ->
  nv (PArray.length (pre_loop degA nI i acc pos H)) = n /\
  forall v, v < n -> rd (pre_loop degA nI i acc pos H) v = ofs v.
Proof.
  intros degA nI HnI Hd z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i acc pos H Hz Hi Hacc Hl Hinv.
  rewrite pre_loop_eq. destruct (bdec (i <? nI)%uint63) as [Hlt | Hge].
  - pose proof (ltb_true _ _ Hlt) as Hlt'. rewrite HnI in Hlt'.
    pose proof (nv_lt i).
    assert (Hi1 : nv (i + 1)%uint63 = nv i + 1) by (apply nv_add_N; rewrite nv_1; lia).
    pose proof (ofs_end (nv i) Hlt').
    eapply IH; [ | reflexivity | | | | ].
    + rewrite <- Hz. apply dec_step. exact Hlt.
    + lia.
    + rewrite Hi1. rewrite nv_add_N; rewrite <- rd_nv, Hd, Hacc by exact Hlt'.
      * rewrite ofs_D. unfold ofs. f_equal. f_equal. lia.
      * lia.
    + rewrite alength_set. exact Hl.
    + intros v Hv. rewrite Hi1 in Hv. destruct (N.eq_dec v (nv i)) as [-> | Ne].
      * rewrite rd_set_same by (reflexivity || lia). exact Hacc.
      * rewrite rd_set_other by lia. apply Hinv. lia.
  - pose proof (ltb_false _ _ Hge). rewrite HnI in H0.
    split; [exact Hl|]. intros v Hv. apply Hinv. lia.
Qed.

Definition cnt (q : nat) (v : N) : nat := count_occ N.eq_dec (firstn q HE) v.

Definition fill_inv (q : nat) (pos adj : array int) : Prop :=
  nv (PArray.length pos) = n /\ nv (PArray.length adj) = N.of_nat (2 * m) /\
  (forall v, v < n -> rd pos v = ofs v + N.of_nat (cnt q v)) /\
  (forall v s, v < n -> ofs v <= s < ofs v + N.of_nat (cnt q v) ->
     rd adj s < N.of_nat q /\ nth (N.to_nat (rd adj s)) HE 0 = v) /\
  (forall p, (p < q)%nat -> exists s,
     ofs (nth p HE 0) <= s < ofs (nth p HE 0) + N.of_nat (cnt q (nth p HE 0)) /\
     rd adj s = N.of_nat p).

Lemma cnt_le_D : forall q v, (cnt q v <= D v)%nat.
Proof. intros q v. apply count_firstn_le. Qed.

Lemma fill_spec : forall col cl base baseI,
  arr_is col cl -> List.length cl = m ->
  (forall i, (i < m)%nat -> nth i cl 0 = nth (base + i) HE 0) ->
  (base + m <= 2 * m)%nat -> nv baseI = N.of_nat base ->
  forall z i pos adj H, gap mI i = z -> nv i <= N.of_nat m ->
  fill_inv (base + N.to_nat (nv i)) pos adj ->
  fill_inv (base + m) (fst (fill_loop col baseI mI i pos adj H))
                      (snd (fill_loop col baseI mI i pos adj H)).
Proof.
  intros col cl base baseI Hc Hl Hcl Hb HbI z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i pos adj H Hz Hi (Lp & La & J1 & J2 & J3).
  rewrite fill_loop_eq. destruct (bdec (i <? mI)%uint63) as [Hlt | Hge].
  - pose proof (ltb_true _ _ Hlt) as Hlt'. rewrite HmI in Hlt'.
    cbv zeta.
    pose proof (nv_lt i).
    assert (Hi1 : nv (i + 1)%uint63 = nv i + 1) by (apply nv_add_N; rewrite nv_1; lia).
    set (q := (base + N.to_nat (nv i))%nat) in *.
    assert (Hq : (q < 2 * m)%nat) by (unfold q; lia).
    assert (Ex : nv col.[i] = nth q HE 0).
    { rewrite arr_get with (l := cl) by (auto; lia). unfold q. apply Hcl. lia. }
    set (x := nth q HE 0) in *.
    assert (Bx : x < n) by (apply HE_lt; exact Hq).
    assert (Cs : forall w, cnt (S q) w = (cnt q w + if N.eq_dec x w then 1 else 0)%nat).
    { intros w. unfold cnt. apply count_snoc. rewrite length_app. lia. }
    assert (Ep : nv pos.[col.[i]] = ofs x + N.of_nat (cnt q x)).
    { rewrite <- rd_nv, Ex. apply J1. exact Bx. }
    set (p := ofs x + N.of_nat (cnt q x)) in *.
    assert (Hpx : p < ofs x + N.of_nat (D x)).
    { pose proof (cnt_le_D (S q) x). rewrite Cs in H1.
      destruct (N.eq_dec x x); [|contradiction]. unfold p. lia. }
    pose proof (ofs_end x Bx) as Endx.
    assert (Eb : nv (baseI + i)%uint63 = N.of_nat q).
    { rewrite nv_add_N; rewrite HbI; unfold q; lia. }
    assert (Rng : forall v s, v < n -> ofs v <= s < ofs v + N.of_nat (cnt (S q) v) ->
                  ofs v <= s < ofs v + N.of_nat (D v)).
    { intros v s Hv Hs. pose proof (cnt_le_D (S q) v). lia. }
    eapply IH; [ | reflexivity | | ].
    + rewrite <- Hz. apply dec_step. exact Hlt.
    + lia.
    + replace (base + N.to_nat (nv (i + 1)%uint63))%nat with (S q) by (unfold q; lia).
      split; [rewrite alength_set; exact Lp|].
      split; [rewrite alength_set; exact La|].
      split; [|split].
      * intros v Hv. rewrite Cs. destruct (N.eq_dec x v) as [<- | Ne].
        -- rewrite rd_set_same by (rewrite ?Lp; lia).
           rewrite nv_add_N; rewrite ?nv_1, Ep; [unfold p; lia | lia].
        -- rewrite rd_set_other by lia. rewrite J1 by exact Hv. lia.
      * intros v s Hv Hs. destruct (N.eq_dec s p) as [-> | Nsp].
        -- assert (Evx : v = x) by (apply (ofs_disj v x p Hv Bx); [apply (Rng v p Hv Hs) | unfold p in *; lia]).
           subst v. rewrite rd_set_same by (rewrite ?La; lia).
           rewrite Eb. split; [lia|]. rewrite Nat2N.id. reflexivity.
        -- rewrite rd_set_other by (pose proof (ofs_end v Hv); pose proof (Rng v s Hv Hs); lia).
           assert (Hs' : ofs v <= s < ofs v + N.of_nat (cnt q v)).
           { rewrite Cs in Hs. destruct (N.eq_dec x v) as [<- | Ne]; [unfold p in *; lia | lia]. }
           destruct (J2 v s Hv Hs') as [A1 A2]. split; [lia | exact A2].
      * intros p' Hp'. destruct (Nat.eq_dec p' q) as [-> | Npq].
        -- exists p. fold x. split; [rewrite Cs; destruct (N.eq_dec x x); [unfold p; lia | contradiction]|].
           rewrite rd_set_same by (rewrite ?La; lia). exact Eb.
        -- destruct (J3 p' ltac:(lia)) as (s & Hs & Es).
           set (y := nth p' HE 0) in *.
           assert (By : y < n) by (apply HE_lt; lia).
           assert (Nsp : s <> p).
           { intros ->. destruct (N.eq_dec y x) as [Eyx | Nyx].
             - rewrite Eyx in Hs. unfold p in Hs. lia.
             - apply Nyx. apply (ofs_disj y x p By Bx); [pose proof (cnt_le_D q y); lia | lia]. }
           exists s. split; [rewrite Cs; lia|].
           rewrite rd_set_other by (pose proof (ofs_end y By); pose proof (cnt_le_D q y); lia).
           exact Es.
  - pose proof (ltb_false _ _ Hge). rewrite HmI in H0.
    replace (base + N.to_nat (nv i))%nat with (base + m)%nat in * by lia.
    simpl. split; [exact Lp|]. split; [exact La|]. auto.
Qed.

(* the other end of half-edge p, and its passageway *)
Definition oth (p : nat) : N := if (p <? m)%nat then nth p eb 0 else nth (p - m) ea 0.
Definition edg (p : nat) : nat := if (p <? m)%nat then p else (p - m)%nat.

(* passageway j joins v and w, in one direction or the other *)
Definition orient (j : nat) (v w : N) : Prop :=
  (nth j ea 0 = v /\ nth j eb 0 = w) \/ (nth j ea 0 = w /\ nth j eb 0 = v).

Lemma half_orient : forall p, (p < 2 * m)%nat ->
  (edg p < m)%nat /\ orient (edg p) (nth p HE 0) (oth p).
Proof.
  intros p Hp. unfold edg, oth, orient. destruct (Nat.ltb_spec p m).
  - split; [lia|]. left. rewrite app_nth1 by lia. auto.
  - split; [lia|]. right. rewrite app_nth2 by lia. rewrite Hea. auto.
Qed.

Lemma oth_lt : forall p, (p < 2 * m)%nat -> oth p < n.
Proof.
  intros p Hp. unfold oth. destruct (Nat.ltb_spec p m);
    apply forall_nth_lt; auto; lia.
Qed.

Lemma other_nv : forall hh, nv hh < N.of_nat (2 * m) ->
  nv (other eaA ebA mI hh) = oth (N.to_nat (nv hh)).
Proof.
  intros hh Hh. unfold other, oth. rewrite ltb_nv, HmI.
  destruct (N.ltb_spec (nv hh) (N.of_nat m)); destruct (Nat.ltb_spec (N.to_nat (nv hh)) m); try lia.
  - apply arr_get; [exact HebA | lia].
  - rewrite arr_get with (l := ea); [| exact HeaA | rewrite nv_sub; rewrite HmI; lia].
    rewrite nv_sub by (rewrite HmI; lia). rewrite HmI. f_equal. lia.
Qed.

Definition upd (f : N -> N) (w v : N) : N -> N := fun x => if N.eqb x w then v else f x.
Definition updn (f : N -> nat) (w : N) (j : nat) : N -> nat :=
  fun x => if N.eqb x w then j else f x.

Lemma nodup_snoc : forall (l : list N) x, NoDup l -> ~ In x l -> NoDup (l ++ [x]).
Proof.
  intros l x Hl Hx. apply NoDup_app; auto. constructor; [simpl; tauto | constructor].
  intros y Hy [<- | []]. contradiction.
Qed.

Lemma nodup_app_disj : forall (l1 l2 : list N) x, NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
  intros l1 l2 x. induction l1 as [| y l1 IH]; simpl; [tauto|].
  intros Hd0 [<- | Hx] Hx2; inversion Hd0 as [| ? ? Hy Hl]; subst.
  - apply Hy. apply in_or_app. right. exact Hx2.
  - exact (IH Hl Hx Hx2).
Qed.

Section DFS.

Variables (r : N) (adjA posA degA : array int).
Hypothesis Hrn : r < n.
Hypothesis Hfill : fill_inv (2 * m) posA adjA.
Hypothesis Hdeg : forall v, v < n -> rd degA v = N.of_nat (D v).

Lemma cnt_full : forall v, cnt (2 * m) v = D v.
Proof. intros v. unfold cnt, deg. rewrite firstn_all2; [reflexivity | rewrite length_app; lia]. Qed.

Lemma slot_ok : forall v s, v < n -> ofs v <= s < ofs v + N.of_nat (D v) ->
  rd adjA s < N.of_nat (2 * m) /\ nth (N.to_nat (rd adjA s)) HE 0 = v.
Proof.
  intros v s Hv Hs. destruct Hfill as (_ & _ & _ & J2 & _). apply J2; [exact Hv|].
  rewrite cnt_full. exact Hs.
Qed.

Lemma slot_all : forall p, (p < 2 * m)%nat -> exists s,
  ofs (nth p HE 0) <= s < ofs (nth p HE 0) + N.of_nat (D (nth p HE 0)) /\
  rd adjA s = N.of_nat p.
Proof.
  intros p Hp. destruct Hfill as (_ & _ & _ & _ & J3). destruct (J3 p Hp) as (s & Hs & Es).
  exists s. rewrite cnt_full in Hs. auto.
Qed.

Definition core (ord st : list N) (par : N -> N) (pe : N -> nat)
    (mark stk : array int) (sp : int) : Prop :=
  nv (PArray.length mark) = n /\ nv (PArray.length stk) = n /\
  (forall v, v < n -> (rd mark v <> 0 <-> In v (ord ++ st))) /\
  NoDup (ord ++ st) /\ (forall x, In x (ord ++ st) -> x < n) /\
  nv sp = N.of_nat (List.length st) /\
  (forall i, (i < List.length st)%nat -> rd stk (N.of_nat i) = nth i st 0) /\
  par r = r /\
  (forall v, In v (ord ++ st) -> v <> r ->
     In (par v) ord /\ (pe v < m)%nat /\ orient (pe v) v (par v) /\
     (In v ord -> (idx (par v) ord < idx v ord)%nat)) /\
  (forall i, (0 < i < List.length ord)%nat ->
     anc par r (par (nth i ord 0)) (nth (i - 1) ord 0)) /\
  (forall i, (i < List.length st)%nat ->
     anc par r (par (nth i st 0))
       (if (S i <? List.length st)%nat then par (nth (S i) st 0) else last ord r)).

Lemma core_bound : forall ord st par pe mark stk sp,
  core ord st par pe mark stk sp -> (List.length ord + List.length st <= N.to_nat n)%nat.
Proof.
  intros ord st par pe mark stk sp (_ & _ & _ & Hnd & Hb & _).
  rewrite <- length_app. apply nodup_bound; assumption.
Qed.

Lemma core_push : forall ord st par pe mark stk sp v w (wI : int) j,
  core ord st par pe mark stk sp -> In r ord -> In v ord -> last ord r = v ->
  nv wI = w -> w < n -> ~ In w (ord ++ st) -> (j < m)%nat -> orient j w v ->
  core ord (st ++ [w]) (upd par w v) (updn pe w j)
    mark.[wI <- 1%uint63] stk.[sp <- wI] (sp + 1)%uint63.
Proof.
  intros ord st par pe mark stk sp v w wI j
    (L1 & L2 & I2 & Nd & Bd & Sp & St & Pr & I9 & I11 & I12) Hr Hv Hl Ew Hw Nw Hj Ho.
  subst w.
  assert (Bnd : (List.length (ord ++ st) + 1 <= N.to_nat n)%nat).
  { rewrite <- (length_app _ [nv wI]).
    apply nodup_bound; [apply nodup_snoc; assumption|].
    intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx | [<- | []]]; auto. }
  rewrite length_app in Bnd.
  assert (Nwo : ~ In (nv wI) ord) by (intro; apply Nw; apply in_or_app; auto).
  assert (Nws : ~ In (nv wI) st) by (intro; apply Nw; apply in_or_app; auto).
  assert (Nwr : nv wI <> r) by (intros E0; rewrite E0 in Nwo; contradiction).
  assert (Fr : forall x, In x ord -> upd par (nv wI) v x = par x).
  { intros x Hx. unfold upd. destruct (N.eqb_spec x (nv wI)); [subst; contradiction | reflexivity]. }
  assert (Fr' : forall x, In x ord -> x <> r -> In (par x) ord).
  { intros x Hx Hxr. apply (I9 x); [apply in_or_app; auto | exact Hxr]. }
  assert (Fa : forall a b, In b ord -> anc par r a b -> anc (upd par (nv wI) v) r a b).
  { intros a b Hb Ha. apply (anc_frame par _ r (fun x => In x ord)); auto. }
  assert (Ewv : upd par (nv wI) v (nv wI) = v) by (unfold upd; rewrite N.eqb_refl; reflexivity).
  assert (Sr : forall x, In x st -> x <> r).
  { intros x Hx ->. exact (nodup_app_disj _ _ _ Nd Hr Hx). }
  split; [rewrite alength_set; exact L1|].
  split; [rewrite alength_set; exact L2|].
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  - intros u Hu. rewrite app_assoc. rewrite in_app_iff. simpl.
    destruct (N.eq_dec u (nv wI)) as [-> | Ne].
    + rewrite rd_set_same by (reflexivity || lia). rewrite nv_1. split; [auto | lia].
    + rewrite rd_set_other by lia.
      rewrite I2 by exact Hu. split; [auto | intros [H | [H | []]]; [exact H | congruence]].
  - rewrite app_assoc. apply nodup_snoc; assumption.
  - intros x Hx. rewrite app_assoc in Hx. apply in_app_or in Hx.
    destruct Hx as [Hx | [<- | []]]; auto.
  - rewrite length_app. simpl. rewrite nv_add_N; rewrite ?nv_1, Sp; lia.
  - intros i Hi. rewrite length_app in Hi. simpl in Hi.
    destruct (Nat.eq_dec i (List.length st)) as [-> | Ne].
    + rewrite rd_set_same by (rewrite ?Sp; reflexivity || lia).
      rewrite nth_middle. reflexivity.
    + rewrite rd_set_other by (rewrite <- ?nv_Z; lia). rewrite app_nth1 by lia. apply St. lia.
  - unfold upd. destruct (N.eqb_spec r (nv wI)); [congruence | exact Pr].
  - intros x Hx Hxr. rewrite app_assoc in Hx. apply in_app_or in Hx. unfold upd, updn.
    destruct Hx as [Hx | [<- | []]].
    + destruct (N.eqb_spec x (nv wI)) as [-> | Ne]; [contradiction|].
      exact (I9 x Hx Hxr).
    + rewrite N.eqb_refl. split; [exact Hv|]. split; [exact Hj|]. split; [exact Ho|].
      intro; contradiction.
  - intros i Hi. rewrite Fr by (apply nth_In; lia). apply Fa; [apply nth_In; lia|].
    apply I11. exact Hi.
  - intros i Hi. rewrite length_app in Hi. simpl in Hi.
    destruct (Nat.eq_dec i (List.length st)) as [-> | Ne].
    + rewrite nth_middle. rewrite Ewv.
      rewrite length_app. simpl. destruct (Nat.ltb_spec (S (List.length st)) (List.length st + 1)); [lia|].
      rewrite Hl. apply anc_refl.
    + rewrite app_nth1 by lia.
      assert (Ii : In (nth i st 0) st) by (apply nth_In; lia).
      assert (E1 : upd par (nv wI) v (nth i st 0) = par (nth i st 0)).
      { unfold upd. destruct (N.eqb_spec (nth i st 0) (nv wI)) as [E | E];
          [rewrite E in Ii; contradiction | reflexivity]. }
      rewrite E1. rewrite length_app. simpl.
      specialize (I12 i ltac:(lia)).
      destruct (Nat.ltb_spec (S i) (List.length st)) as [Hs | Hs].
      * destruct (Nat.ltb_spec (S i) (List.length st + 1)); [|lia].
        rewrite app_nth1 by lia.
        assert (Is : In (nth (S i) st 0) st) by (apply nth_In; lia).
        assert (E2 : upd par (nv wI) v (nth (S i) st 0) = par (nth (S i) st 0)).
        { unfold upd. destruct (N.eqb_spec (nth (S i) st 0) (nv wI)) as [E | E];
            [rewrite E in Is; contradiction | reflexivity]. }
        rewrite E2. apply Fa; [| exact I12].
        apply (I9 (nth (S i) st 0)); [apply in_or_app; auto | apply Sr; exact Is].
      * destruct (Nat.ltb_spec (S i) (List.length st + 1)); [|lia].
        replace (S i) with (List.length st) by lia. rewrite nth_middle.
        rewrite Ewv.
        apply Fa; [exact Hv | rewrite <- Hl; exact I12].
Qed.

Lemma orient_sym : forall j a b, orient j a b -> orient j b a.
Proof. unfold orient. tauto. Qed.

Lemma nb_spec : forall v eI, v < n -> nv eI = ofs v + N.of_nat (D v) ->
  forall z s ord st par pe mark stk sp H, gap eI s = z ->
  ofs v <= nv s <= ofs v + N.of_nat (D v) ->
  In v ord -> last ord r = v -> In r ord ->
  core ord st par pe mark stk sp ->
  (forall s', ofs v <= s' < nv s -> In (oth (N.to_nat (rd adjA s'))) (ord ++ st)) ->
  exists st' par' pe',
    core ord (st ++ st') par' pe'
      (fst (fst (nb_loop eaA ebA adjA mI eI s mark stk sp H)))
      (snd (fst (nb_loop eaA ebA adjA mI eI s mark stk sp H)))
      (snd (nb_loop eaA ebA adjA mI eI s mark stk sp H)) /\
    (forall s', ofs v <= s' < ofs v + N.of_nat (D v) ->
       In (oth (N.to_nat (rd adjA s'))) (ord ++ st ++ st')).
Proof.
  intros v eI Hv HeI z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros s ord st par pe mark stk sp H Hz Hs Hvo Hl Hr C Cl.
  rewrite nb_loop_eq. destruct (bdec (s <? eI)%uint63) as [Hlt | Hge].
  - pose proof (ltb_true _ _ Hlt) as Hlt'. rewrite HeI in Hlt'.
    pose proof (ofs_end v Hv) as Ev.
    assert (Hs1 : nv (s + 1)%uint63 = nv s + 1) by (apply nv_add_N; rewrite nv_1; lia).
    destruct (slot_ok v (nv s) Hv ltac:(lia)) as [Ha He].
    rewrite rd_nv in Ha, He.
    set (p := N.to_nat (nv adjA.[s])) in *.
    assert (Hp : (p < 2 * m)%nat) by (unfold p; lia).
    assert (Ew : nv (other eaA ebA mI adjA.[s]) = oth p) by (apply other_nv; exact Ha).
    destruct (half_orient p Hp) as [Hj Ho]. rewrite He in Ho.
    pose proof (oth_lt p Hp) as Bw.
    pose proof C as (L1 & L2 & I2 & _).
    cbv zeta.
    destruct (mark.[other eaA ebA mI adjA.[s]] =? 0)%uint63 eqn:Em.
    + rewrite eqb_nv, nv_0 in Em. apply N.eqb_eq in Em. rewrite <- rd_nv, Ew in Em.
      assert (Nw : ~ In (oth p) (ord ++ st)) by (intro I; apply (proj2 (I2 _ Bw)) in I; contradiction).
      pose proof (core_push ord st par pe mark stk sp v (oth p) _ (edg p) C Hr Hvo Hl Ew Bw Nw Hj
                    (orient_sym _ _ _ Ho)) as C'.
      edestruct (IH (gap eI (s + 1)%uint63)) as (st'' & par'' & pe'' & C'' & Cl'');
        [rewrite <- Hz; apply dec_step; exact Hlt | reflexivity | rewrite Hs1; lia
        | exact Hvo | exact Hl | exact Hr | exact C' | |].
      * intros s' Hs'. rewrite Hs1 in Hs'. rewrite app_assoc. apply in_or_app.
        destruct (N.eq_dec s' (nv s)) as [-> | Ne].
        -- right. rewrite rd_nv. left. reflexivity.
        -- left. apply Cl. lia.
      * rewrite <- app_assoc in C'', Cl''. simpl in C'', Cl''.
        exists (oth p :: st''), par'', pe''. split; [exact C'' | exact Cl''].
    + rewrite eqb_nv, nv_0 in Em. apply N.eqb_neq in Em. rewrite <- rd_nv, Ew in Em.
      assert (Iw : In (oth p) (ord ++ st)) by (apply (I2 _ Bw); exact Em).
      apply (IH (gap eI (s + 1)%uint63) ltac:(rewrite <- Hz; apply dec_step; exact Hlt)
               (s + 1)%uint63 ord st par pe); [reflexivity | rewrite Hs1; lia | exact Hvo | exact Hl | exact Hr | exact C |].
      intros s' Hs'. rewrite Hs1 in Hs'.
      destruct (N.eq_dec s' (nv s)) as [-> | Ne].
      * rewrite rd_nv. fold p. exact Iw.
      * apply Cl. lia.
  - pose proof (ltb_false _ _ Hge) as Hge'. rewrite HeI in Hge'.
    simpl. exists [], par, pe. rewrite app_nil_r. split; [exact C|].
    intros s' Hs'. apply Cl. lia.
Qed.

Lemma nodup_seqN : forall k, NoDup (map N.of_nat (seq 0 k)).
Proof.
  intros k. generalize (seq_NoDup k 0). generalize (seq 0 k). intros l Hl.
  induction Hl as [| x l Hx Hl IH]; simpl; constructor; [| exact IH].
  intros H. apply in_map_iff in H. destruct H as (y & Ey & Hy).
  assert (y = x) by lia. subst. contradiction.
Qed.

Lemma nth_last : forall (l : list N) d, l <> [] -> nth (List.length l - 1) l d = last l d.
Proof.
  intros l d H. destruct (exists_last H) as (l' & a & ->).
  rewrite length_app, last_last. simpl. replace (List.length l' + 1 - 1)%nat with (List.length l') by lia.
  rewrite nth_middle. reflexivity.
Qed.

Lemma last_default : forall (l : list N) d d', l <> [] -> last l d = last l d'.
Proof.
  intros l d d' H. destruct (exists_last H) as (l' & a & ->). rewrite !last_last. reflexivity.
Qed.

Lemma core_pop : forall ord st0 v par pe mark stk sp,
  core ord (st0 ++ [v]) par pe mark stk sp ->
  core (ord ++ [v]) st0 par pe mark stk (sp - 1)%uint63.
Proof.
  intros ord st0 v par pe mark stk sp
    (L1 & L2 & I2 & Nd & Bd & Sp & St & Pr & I9 & I11 & I12).
  rewrite length_app in Sp. simpl in Sp.
  assert (Eq : forall u, In u ((ord ++ [v]) ++ st0) <-> In u (ord ++ st0 ++ [v])).
  { intros u. rewrite !in_app_iff. tauto. }
  assert (Nd' : NoDup ((ord ++ [v]) ++ st0)).
  { apply (Permutation_NoDup (l := ord ++ st0 ++ [v])); [|exact Nd].
    rewrite <- app_assoc. apply Permutation_app_head. apply Permutation_app_comm. }
  assert (Nvo : ~ In v ord).
  { intros I. apply (nodup_app_disj _ _ _ Nd I). apply in_or_app. right. left. reflexivity. }
  split; [exact L1|]. split; [exact L2|].
  split; [|split; [exact Nd'|split; [|split; [|split; [|split; [exact Pr|split; [|split]]]]]]].
  - intros u Hu. rewrite Eq. apply I2. exact Hu.
  - intros x Hx. apply Bd. apply Eq. exact Hx.
  - rewrite nv_sub; rewrite nv_1; lia.
  - intros i Hi. rewrite St by (rewrite length_app; simpl; lia). apply app_nth1. exact Hi.
  - intros x Hx Hxr. destruct (I9 x (proj1 (Eq x) Hx) Hxr) as (A1 & A2 & A3 & A4).
    split; [apply in_or_app; left; exact A1|]. split; [exact A2|]. split; [exact A3|].
    intros Ix. rewrite (idx_app_l (par x)) by exact A1.
    apply in_app_or in Ix. destruct Ix as [Ix | [<- | []]].
    + rewrite idx_app_l by exact Ix. apply A4. exact Ix.
    + rewrite idx_app_r by exact Nvo. simpl. rewrite N.eqb_refl.
      pose proof (idx_lt _ _ A1). lia.
  - intros i Hi. rewrite length_app in Hi. simpl in Hi.
    destruct (Nat.eq_dec i (List.length ord)) as [-> | Ne].
    + rewrite nth_middle. rewrite app_nth1 by lia.
      assert (Ho : ord <> []) by (intros ->; simpl in Hi; lia).
      rewrite nth_last by exact Ho. rewrite (last_default ord 0 r Ho).
      specialize (I12 (List.length st0) ltac:(rewrite length_app; simpl; lia)).
      rewrite nth_middle, length_app in I12. simpl in I12.
      destruct (Nat.ltb_spec (S (List.length st0)) (List.length st0 + 1)); [lia|]. exact I12.
    + rewrite !app_nth1 by lia. apply I11. lia.
  - intros i Hi. rewrite last_last.
    specialize (I12 i ltac:(rewrite length_app; simpl; lia)).
    rewrite app_nth1 in I12 by lia. rewrite length_app in I12. simpl in I12.
    destruct (Nat.ltb_spec (S i) (List.length st0 + 1)); [|lia].
    destruct (Nat.ltb_spec (S i) (List.length st0)) as [Hs | Hs].
    + rewrite app_nth1 in I12 by lia. exact I12.
    + replace (S i) with (List.length st0) in I12 by lia. rewrite nth_middle in I12.
      apply (anc_trans _ _ _ _ _ I12).
      destruct (anc_par par r v) as [A | ->]; [exact A | rewrite Pr; apply anc_refl].
Qed.

Definition outer (ord st : list N) par pe mark stk sp (lv : array int) (L t : int) : Prop :=
  core ord st par pe mark stk sp /\
  nv (PArray.length lv) = n /\
  nv t = N.of_nat (List.length ord) /\
  nv L = N.of_nat (List.length (leaves ea eb ord)) /\
  (forall i, (i < List.length (leaves ea eb ord))%nat ->
     rd lv (N.of_nat i) = nth i (leaves ea eb ord) 0) /\
  (ord = [] -> st = [r]) /\ (ord <> [] -> nth 0 ord 0 = r) /\
  (forall u, In u ord -> forall p, (p < 2 * m)%nat -> nth p HE 0 = u ->
     In (oth p) (ord ++ st)).

Definition fin (ord : list N) (par : N -> N) (pe : N -> nat) : Prop :=
  NoDup ord /\ (forall x, In x ord <-> x < n) /\ List.length ord = S m /\
  nth 0 ord 0 = r /\ par r = r /\
  (forall v, v < n -> v <> r ->
    (pe v < m)%nat /\ par v < n /\ (idx (par v) ord < idx v ord)%nat /\
    ((nth (pe v) ea 0 = v /\ nth (pe v) eb 0 = par v) \/
     (nth (pe v) ea 0 = par v /\ nth (pe v) eb 0 = v))) /\
  (forall i, (0 < i < S m)%nat -> anc par r (par (nth i ord 0)) (nth (i - 1) ord 0)).

Lemma fin_of : forall ord st par pe mark stk sp,
  core ord st par pe mark stk sp -> ord <> [] -> nth 0 ord 0 = r ->
  (forall x, x < n -> In x ord) -> fin ord par pe.
Proof.
  intros ord st par pe mark stk sp (L1 & L2 & I2 & Nd & Bd & Sp & St & Pr & I9 & I11 & I12)
    Hne H0 Hall.
  assert (Nd' : NoDup ord) by exact (NoDup_app_remove_r _ _ Nd).
  assert (Bo : forall x, In x ord -> x < n) by (intros x Hx; apply Bd; apply in_or_app; auto).
  assert (Hlen : List.length ord = S m).
  { pose proof (nodup_bound ord n Nd' Bo).
    assert (Hi : incl (map N.of_nat (seq 0 (N.to_nat n))) ord).
    { intros x Hx. apply in_map_iff in Hx. destruct Hx as (k & <- & Hk). apply in_seq in Hk.
      apply Hall. lia. }
    pose proof (NoDup_incl_length (nodup_seqN (N.to_nat n)) Hi). rewrite length_map, length_seq in H1. lia. }
  split; [exact Nd'|]. split; [intros x; split; [apply Bo | apply Hall]|].
  split; [exact Hlen|]. split; [exact H0|]. split; [exact Pr|]. split.
  - intros v Hv Hvr. destruct (I9 v ltac:(apply in_or_app; left; apply Hall; exact Hv) Hvr)
      as (A1 & A2 & A3 & A4).
    split; [exact A2|]. split; [apply Bo; exact A1|]. split; [apply A4; apply Hall; exact Hv|].
    exact A3.
  - intros i Hi. apply I11. lia.
Qed.

Lemma filter_len : forall (f : N -> bool) (l : list N), (List.length (filter f l) <= List.length l)%nat.
Proof. intros f l. induction l as [| x l IH]; simpl; [lia|]. destruct (f x); simpl; lia. Qed.

Lemma nodup_full : forall l, NoDup l -> (forall x, In x l -> x < n) ->
  List.length l = N.to_nat n -> forall x, x < n -> In x l.
Proof.
  intros l Hnd Hb Hl x Hx.
  assert (I : In (N.to_nat x) (map N.to_nat l)).
  { apply (pigeon _ (N.to_nat n)); [| rewrite length_map; exact Hl | | lia].
    - apply nodup_map_inj; [exact Hnd|]. intros a b _ _ E. lia.
    - intros k Hk. apply in_map_iff in Hk. destruct Hk as (y & <- & Hy). specialize (Hb y Hy). lia. }
  apply in_map_iff in I. destruct I as (y & Ey & Hy). replace x with y by lia. exact Hy.
Qed.

Lemma tree_closed : is_tree n (combine ea eb) -> forall ord, In r ord ->
  (forall u, In u ord -> forall p, (p < 2 * m)%nat -> nth p HE 0 = u -> In (oth p) ord) ->
  forall x, x < n -> In x ord.
Proof.
  intros Ht ord Hr Cl x Hx.
  destruct (Ht r x Hrn Hx) as (l & (R1 & R2 & R3 & R4) & _).
  assert (Step : forall a b, In a ord -> joined (combine ea eb) a b -> In b ord).
  { intros a b Ha [J | J]; destruct (In_nth _ _ (0, 0) J) as (j & Hj & Ej);
      rewrite length_combine, Hea, Heb, Nat.min_id in Hj;
      rewrite nth_combine_N in Ej by lia; injection Ej as E1 E2.
    - replace b with (oth j) by (unfold oth; destruct (Nat.ltb_spec j m); [exact E2 | lia]).
      apply (Cl a Ha); [lia|]. rewrite app_nth1 by lia. exact E1.
    - replace b with (oth (m + j)) by (unfold oth; destruct (Nat.ltb_spec (m + j) m);
        [lia | replace (m + j - m)%nat with j by lia; exact E1]).
      apply (Cl a Ha); [lia|]. rewrite app_nth2 by lia. rewrite Hea.
      replace (m + j - m)%nat with j by lia. exact E2. }
  assert (G : forall l, linked (combine ea eb) l -> (forall y, hd_error l = Some y -> In y ord) ->
            forall z, In z l -> In z ord).
  { intros l0. induction l0 as [| a l0 IH]; intros Hli Hh z Hz; [destruct Hz|].
    assert (Ia : In a ord) by (apply Hh; reflexivity).
    destruct Hz as [<- | Hz]; [exact Ia|].
    apply linked_cons in Hli. destruct Hli as [J Hli].
    apply IH; [exact Hli | | exact Hz].
    intros y Hy. destruct l0 as [| b l0]; [discriminate|]. simpl in Hy. injection Hy as <-.
    exact (Step a b Ia J). }
  apply (G l R2); [intros y Hy; rewrite R3 in Hy; injection Hy as <-; exact Hr|].
  apply in_rev. destruct (rev l) as [| y t]; [discriminate|]. simpl in R4. injection R4 as ->.
  left. reflexivity.
Qed.

Lemma dfs_spec : forall nI, nv nI = n -> is_tree n (combine ea eb) ->
  forall z t ord st par pe mark stk sp lv L H, gap nI t = z ->
  outer ord st par pe mark stk sp lv L t ->
  exists ord' par' pe', fin ord' par' pe' /\
    nv (PArray.length (fst (dfs_loop eaA ebA adjA degA posA nI mI t mark stk sp lv L H))) = n /\
    nv (snd (dfs_loop eaA ebA adjA degA posA nI mI t mark stk sp lv L H))
      = N.of_nat (List.length (leaves ea eb ord')) /\
    (forall i, (i < List.length (leaves ea eb ord'))%nat ->
       rd (fst (dfs_loop eaA ebA adjA degA posA nI mI t mark stk sp lv L H)) (N.of_nat i)
       = nth i (leaves ea eb ord') 0).
Proof.
  intros nI HnI Ht z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros t ord st par pe mark stk sp lv L H Hz O.
  pose proof O as (C & Llv & Et & EL & Elv & I7a & I7b & Cl).
  pose proof (core_bound _ _ _ _ _ _ _ C) as Bnd.
  rewrite dfs_loop_eq. destruct (bdec (t <? nI)%uint63) as [Hlt | Hge].
  - pose proof (ltb_true _ _ Hlt) as Hlt'. rewrite HnI in Hlt'.
    destruct (0 <? sp)%uint63 eqn:Esp.
    + pose proof C as (L1 & L2 & I2 & Nd & Bd & Sp & St & Pr & _).
      apply ltb_true in Esp. rewrite nv_0 in Esp.
      assert (Hst : st <> []) by (intros ->; simpl in Sp; lia).
      destruct (exists_last Hst) as (st0 & v & Est). subst st.
      rewrite length_app in Sp, Bnd. simpl in Sp, Bnd.
      assert (Esp1 : nv (sp - 1)%uint63 = N.of_nat (List.length st0)) by (rewrite nv_sub; rewrite nv_1; lia).
      assert (Ev : nv stk.[(sp - 1)%uint63] = v).
      { rewrite <- rd_nv, Esp1, St by (rewrite length_app; simpl; lia). apply nth_middle. }
      assert (Bv : v < n) by (apply Bd; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
      assert (Edv : nv degA.[stk.[(sp - 1)%uint63]] = N.of_nat (D v)) by (rewrite <- rd_nv, Ev; apply Hdeg; exact Bv).
      assert (Ee : nv posA.[stk.[(sp - 1)%uint63]] = ofs v + N.of_nat (D v)).
      { rewrite <- rd_nv, Ev. destruct Hfill as (_ & _ & J1 & _). rewrite J1 by exact Bv.
        rewrite cnt_full. reflexivity. }
      assert (Eb : nv (posA.[stk.[(sp - 1)%uint63]] - degA.[stk.[(sp - 1)%uint63]])%uint63 = ofs v)
        by (rewrite nv_sub; rewrite Ee, Edv; lia).
      pose proof (core_pop _ _ _ _ _ _ _ _ C) as C1.
      assert (Hvo : In v (ord ++ [v])) by (apply in_or_app; right; left; reflexivity).
      assert (Hlast : last (ord ++ [v]) r = v) by apply last_last.
      assert (Hro : ord = [] -> v = r).
      { intros E0. specialize (I7a E0). destruct st0 as [| a st0]; [injection I7a; auto|].
        apply (f_equal (@List.length N)) in I7a. rewrite length_app in I7a. simpl in I7a. lia. }
      assert (Hr0 : nth 0 (ord ++ [v]) 0 = r).
      { destruct ord as [| a ord]; [simpl; apply Hro; reflexivity|].
        simpl. apply I7b. discriminate. }
      assert (Hr : In r (ord ++ [v])) by (rewrite <- Hr0; apply nth_In; rewrite length_app; simpl; lia).
      destruct (nb_spec v _ Bv Ee _ _ (ord ++ [v]) st0 par pe mark stk (sp - 1)%uint63
                  (Zwf_well_founded 0 (gap posA.[stk.[(sp - 1)%uint63]]
                     (posA.[stk.[(sp - 1)%uint63]] - degA.[stk.[(sp - 1)%uint63]])%uint63))
                  eq_refl ltac:(rewrite Eb; lia) Hvo Hlast Hr C1
                  ltac:(intros s' Hs'; rewrite Eb in Hs'; lia))
        as (st' & par' & pe' & C' & Clv).
      cbv zeta.
      destruct (nb_loop eaA ebA adjA mI posA.[stk.[(sp - 1)%uint63]]
                  (posA.[stk.[(sp - 1)%uint63]] - degA.[stk.[(sp - 1)%uint63]])%uint63 mark stk
                  (sp - 1)%uint63
                  (Zwf_well_founded 0 (gap posA.[stk.[(sp - 1)%uint63]]
                     (posA.[stk.[(sp - 1)%uint63]] - degA.[stk.[(sp - 1)%uint63]])%uint63)))
        as [[mark' stk'] sp'] eqn:Enb.
      simpl in C'.
      assert (Ed1 : (degA.[stk.[(sp - 1)%uint63]] =? 1)%uint63 = Nat.eqb (D v) 1).
      { rewrite eqb_nv, Edv, nv_1. destruct (N.eqb_spec (N.of_nat (D v)) 1);
          destruct (Nat.eqb_spec (D v) 1); lia. }
      assert (Elf : leaves ea eb (ord ++ [v]) =
                    leaves ea eb ord ++ (if Nat.eqb (D v) 1 then [v] else [])).
      { unfold leaves. rewrite filter_app. simpl. reflexivity. }
      pose proof (filter_len (fun v0 => Nat.eqb (D v0) 1) ord) as Fl. fold (leaves ea eb ord) in Fl.
      pose proof (nv_lt t).
      apply (IH (gap nI (t + 1)%uint63) ltac:(rewrite <- Hz; apply dec_step; exact Hlt)
               (t + 1)%uint63 (ord ++ [v]) (st0 ++ st') par' pe'); [reflexivity|].
      split; [exact C'|]. split; [|split; [|split; [|split; [|split; [|split]]]]].
      * rewrite Ed1. destruct (Nat.eqb (D v) 1); [rewrite alength_set|]; exact Llv.
      * rewrite length_app. simpl. rewrite nv_add_N; rewrite ?nv_1; lia.
      * rewrite Elf, Ed1. destruct (Nat.eqb (D v) 1).
        -- rewrite length_app. simpl. rewrite nv_add_N; rewrite ?nv_1; lia.
        -- rewrite app_nil_r. exact EL.
      * rewrite Elf, Ed1. destruct (Nat.eqb (D v) 1).
        -- intros i Hi. rewrite length_app in Hi. simpl in Hi.
           destruct (Nat.eq_dec i (List.length (leaves ea eb ord))) as [-> | Ne].
           ++ rewrite rd_set_same by (rewrite ?Llv; lia). rewrite nth_middle. exact Ev.
           ++ rewrite rd_set_other by lia. rewrite app_nth1 by lia. apply Elv. lia.
        -- rewrite app_nil_r. exact Elv.
      * intros E0. destruct ord; discriminate.
      * intros _. exact Hr0.
      * intros u Hu p Hp Ep. apply in_app_or in Hu. destruct Hu as [Hu | [<- | []]].
        -- pose proof (Cl u Hu p Hp Ep) as I. rewrite !in_app_iff in I. rewrite !in_app_iff.
           simpl in I |- *. tauto.
        -- destruct (slot_all p Hp) as (s & Hs & Es). rewrite Ep in Hs.
           pose proof (Clv s Hs) as I. rewrite Es, Nat2N.id in I. exact I.
    + apply ltb_false in Esp. rewrite nv_0 in Esp.
      pose proof C as (_ & _ & _ & _ & _ & Sp & _).
      assert (Hst : st = []) by (destruct st; [reflexivity | simpl in Sp; lia]). subst st.
      assert (Ho : ord <> []) by (intros E0; specialize (I7a E0); discriminate).
      simpl. exists ord, par, pe. split; [|split; [exact Llv | split; [exact EL | exact Elv]]].
      apply (fin_of ord [] par pe mark stk sp C Ho (I7b Ho)).
      apply tree_closed; [exact Ht | rewrite <- (I7b Ho); apply nth_In; destruct ord; [contradiction | simpl; lia]|].
      intros u Hu p Hp Ep. rewrite <- (app_nil_r ord). exact (Cl u Hu p Hp Ep).
  - pose proof (ltb_false _ _ Hge) as Hge'. rewrite HnI in Hge'.
    simpl. exists ord, par, pe. split; [|split; [exact Llv | split; [exact EL | exact Elv]]].
    pose proof C as (_ & _ & _ & Nd & Bd & _).
    assert (Hl : List.length ord = N.to_nat n) by lia.
    assert (Ho : ord <> []) by (intros ->; simpl in Hl; lia).
    apply (fin_of ord st par pe mark stk sp C Ho (I7b Ho)).
    apply nodup_full; [exact (NoDup_app_remove_r _ _ Nd) | intros x Hx; apply Bd; apply in_or_app; auto | exact Hl].
Qed.

End DFS.

Lemma root_spec : forall degA nI, nv nI = n ->
  forall z i H, gap nI i = z -> nv (root_loop degA nI i H) < n.
Proof.
  intros degA nI HnI z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i H Hz. rewrite root_loop_eq. destruct (bdec (i <? nI)%uint63) as [Hlt | Hge].
  - pose proof (ltb_true _ _ Hlt) as Hlt'. rewrite HnI in Hlt'.
    destruct (2 <=? degA.[i])%uint63; [exact Hlt'|].
    apply (IH (gap nI (i + 1)%uint63)); [rewrite <- Hz; apply dec_step; exact Hlt | reflexivity].
  - rewrite nv_0. lia.
Qed.

End Machine.

Lemma out_spec : forall (Lv : list N) lvA aI cI,
  N.of_nat (List.length Lv) < 4194304 ->
  (forall k, (k < List.length Lv)%nat -> rd lvA (N.of_nat k) = nth k Lv 0) ->
  nv aI = N.of_nat (List.length Lv / 2) ->
  nv cI = N.of_nat (List.length Lv - List.length Lv / 2) ->
  forall z i xs ys H, gap cI i = z -> nv i <= nv cI ->
  nv (PArray.length xs) = nv cI -> nv (PArray.length ys) = nv cI ->
  (forall k, k < nv i -> rd xs k = nth (N.to_nat k) Lv 0 /\
                         rd ys k = nth (N.to_nat k + List.length Lv / 2) Lv 0) ->
  arr_is (fst (out_loop lvA aI cI i xs ys H)) (firstn (List.length Lv - List.length Lv / 2) Lv) /\
  arr_is (snd (out_loop lvA aI cI i xs ys H)) (skipn (List.length Lv / 2) Lv).
Proof.
  intros Lv lvA aI cI HLb Hlv HaI HcI z.
  set (L := List.length Lv) in *. set (a := (L / 2)%nat) in *.
  assert (Ha : (a <= L)%nat) by (unfold a; apply Nat.Div0.div_le_upper_bound; lia).
  assert (Hca : (L - a <= a + 1)%nat).
  { unfold a. pose proof (Nat.div_mod L 2 ltac:(lia)). pose proof (Nat.mod_upper_bound L 2 ltac:(lia)). lia. }
  assert (EL : L = List.length Lv) by reflexivity.
  clearbody a L.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i xs ys H Hz Hi Lx Ly Hinv.
  rewrite out_loop_eq. destruct (bdec (i <? cI)%uint63) as [Hlt | Hge].
  - pose proof (ltb_true _ _ Hlt) as Hlt'.
    pose proof (nv_lt cI).
    assert (Hi1 : nv (i + 1)%uint63 = nv i + 1) by (apply nv_add_N; rewrite nv_1; lia).
    assert (Hia : nv (i + aI)%uint63 = nv i + N.of_nat a)
      by (rewrite nv_add_N; [rewrite HaI; reflexivity | lia]).
    apply (IH (gap cI (i + 1)%uint63)); [rewrite <- Hz; apply dec_step; exact Hlt | reflexivity
      | lia | rewrite alength_set; exact Lx | rewrite alength_set; exact Ly |].
    intros k Hk. rewrite Hi1 in Hk.
    destruct (N.eq_dec k (nv i)) as [-> | Ne].
    + rewrite !rd_set_same by (rewrite ?Lx, ?Ly; reflexivity || lia).
      rewrite <- !rd_nv. rewrite Hia.
      rewrite <- (N2Nat.id (nv i)) at 1. rewrite Hlv by lia.
      replace (nv i + N.of_nat a) with (N.of_nat (N.to_nat (nv i) + a)) by lia.
      rewrite Hlv by lia. auto.
    + rewrite !rd_set_other by lia. apply Hinv. lia.
  - pose proof (ltb_false _ _ Hge). simpl.
    assert (Hk : forall k, (k < L - a)%nat ->
              rd xs (N.of_nat k) = nth k Lv 0 /\ rd ys (N.of_nat k) = nth (k + a) Lv 0).
    { intros k Hk. pose proof (Hinv (N.of_nat k) ltac:(lia)) as E. rewrite Nat2N.id in E. exact E. }
    split; split.
    + rewrite Lx, HcI, length_firstn. f_equal. lia.
    + intros k Hk'. rewrite length_firstn in Hk'. rewrite nth_firstn.
      destruct (Nat.ltb_spec k (L - a)); [|lia]. apply Hk. lia.
    + rewrite Ly, HcI, length_skipn. rewrite EL. reflexivity.
    + intros k Hk'. rewrite length_skipn in Hk'. rewrite nth_skipn.
      rewrite Nat.add_comm. apply Hk. lia.
Qed.

Lemma arr_repr : forall (a : array uint) (l : list N), arr_is a l -> repr a l.
Proof.
  intros a l [Hl Hc]. split.
  - assert (G : forall z : int, nv z = N.of_nat (List.length l) -> Z.of_nat (List.length l) = (φ z))
      by (intros z Hz; rewrite <- nv_Z; lia).
    apply G. exact Hl.
  - intros k Hk. exists (nth k l 0). split; [apply nth_error_nth'; exact Hk|].
    pose proof (Hc k Hk) as E. unfold rd, nv, ix in E. rewrite nat_N_Z in E. exact E.
Qed.


(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Lemma kingpin_impl_correct :
  forall (n h : N) (ea eb : list N) (n' h' : uint) (ea' eb' : array uint),
  valid_input n h ea eb ->
  repr n' n -> repr h' h -> repr ea' ea -> repr eb' eb ->
  exists o : list N * list N,
    repr (kingpin_impl n' h' ea' eb' : array uint * array uint) o /\
    kingpin_escape_spec n h ea eb o.
Proof.
  intros n h ea eb n' h' ea' eb' Hv Hn' _ Hea' Heb'.
  pose proof Hv as [Vn Vh Va Vb VA VB Vt]. unfold len in Va, Vb.
  set (m := List.length ea) in *.
  assert (Hea : List.length ea = m) by reflexivity.
  assert (Heb : List.length eb = m) by lia.
  assert (Hn : n = N.of_nat m + 1) by lia.
  assert (Hnb : n <= 100000) by lia.
  assert (Hm1 : (1 <= m)%nat) by lia.
  assert (HnI : nv n' = n) by exact Hn'.
  pose proof (repr_arr_is ea' ea Hea') as AeA.
  pose proof (repr_arr_is eb' eb Heb') as AeB.
  clear Hn' Hea' Heb'.
  assert (HmI : nv (n' - 1)%uint63 = N.of_nat m) by (rewrite nv_sub; rewrite ?nv_1; lia).
  unfold kingpin_impl.
  set (mI := (n' - 1)%uint63) in *.
  pose proof (count_occ_bound N.eq_dec 0 ea) as _.
  assert (Cb : forall l v, Forall (fun x => x < n) l -> List.length l = m ->
            (count_occ N.eq_dec l v <= m)%nat).
  { intros l v _ Hl. rewrite <- Hl. apply count_occ_bound. }
  assert (Lmk : nv (PArray.length (PArray.make n' 0%uint63)) = n)
    by (rewrite alength_make; lia).
  (* the degrees *)
  destruct (cnt_spec n m ea eb mI Hea Heb Hn Hnb HmI ea' ea (fun _ => 0) AeA Hea VA
              ltac:(intros v Hv0; cbv beta; pose proof (Cb ea v VA Hea); lia)
              _ 0%uint63 (PArray.make n' 0%uint63) (Zwf_well_founded 0 (gap mI 0%uint63)) eq_refl
              ltac:(rewrite nv_0; lia) Lmk
              ltac:(intros v Hv0; rewrite rd_make; reflexivity))
    as [D0l D0c].
  set (deg0 := cnt_loop ea' mI 0%uint63 (PArray.make n' 0%uint63) (Zwf_well_founded 0 (gap mI 0%uint63))) in *.
  destruct (cnt_spec n m ea eb mI Hea Heb Hn Hnb HmI eb' eb
              (fun v => N.of_nat (count_occ N.eq_dec ea v)) AeB Heb VB
              ltac:(intros v Hv0; cbv beta; pose proof (Cb ea v VA Hea); pose proof (Cb eb v VB Heb); lia)
              _ 0%uint63 deg0 (Zwf_well_founded 0 (gap mI 0%uint63)) eq_refl
              ltac:(rewrite nv_0; lia) D0l
              ltac:(intros v Hv0; rewrite D0c by exact Hv0; simpl; lia))
    as [Dl Dc].
  set (degA := cnt_loop eb' mI 0%uint63 deg0 (Zwf_well_founded 0 (gap mI 0%uint63))) in *.
  assert (Hdeg : forall v, v < n -> rd degA v = N.of_nat (deg ea eb v)).
  { intros v Hv0. rewrite Dc by exact Hv0. unfold deg. rewrite count_occ_app. lia. }
  (* the offsets *)
  destruct (pre_spec n m ea eb mI Hea Heb Hn Hnb VA VB HmI degA n' HnI Hdeg
              _ 0%uint63 0%uint63 (PArray.make n' 0%uint63) (Zwf_well_founded 0 (gap n' 0%uint63))
              eq_refl ltac:(rewrite nv_0; lia) ltac:(rewrite nv_0; reflexivity) Lmk
              ltac:(intros v Hv0; rewrite nv_0 in Hv0; lia))
    as [P0l P0c].
  set (pos0 := pre_loop degA n' 0%uint63 0%uint63 (PArray.make n' 0%uint63) (Zwf_well_founded 0 (gap n' 0%uint63))) in *.
  (* the adjacency *)
  assert (HmmI : nv (mI + mI)%uint63 = N.of_nat (2 * m)) by (rewrite nv_add_N; lia).
  pose proof (fill_spec n m ea eb mI Hea Heb Hn Hnb VA VB HmI ea' ea 0 0%uint63 AeA Hea
                ltac:(intros i Hi; rewrite app_nth1 by lia; reflexivity) ltac:(lia) nv_0
                _ 0%uint63 pos0 (PArray.make (mI + mI)%uint63 0%uint63) (Zwf_well_founded 0 (gap mI 0%uint63))
                eq_refl ltac:(rewrite nv_0; lia)) as F1.
  destruct (fill_loop ea' 0%uint63 mI 0%uint63 pos0 (PArray.make (mI + mI)%uint63 0%uint63) (Zwf_well_founded 0 (gap mI 0%uint63)))
    as [pos1 adj1] eqn:E1.
  simpl in F1.
  assert (F1' : fill_inv n m ea eb (m + N.to_nat (nv 0%uint63)) pos1 adj1).
  { rewrite nv_0. replace (m + N.to_nat 0)%nat with (0 + m)%nat by lia. apply F1.
    split; [exact P0l|]. split; [rewrite alength_make; lia|].
    split; [|split].
    - intros v Hv0. rewrite P0c by exact Hv0. unfold cnt. simpl. lia.
    - intros v s Hv0 Hs. unfold cnt in Hs. simpl in Hs. lia.
    - intros p Hp. lia. }
  clear F1.
  pose proof (fill_spec n m ea eb mI Hea Heb Hn Hnb VA VB HmI eb' eb m mI AeB Heb
                ltac:(intros i Hi; rewrite app_nth2 by lia; f_equal; lia) ltac:(lia) HmI
                _ 0%uint63 pos1 adj1 (Zwf_well_founded 0 (gap mI 0%uint63))
                eq_refl ltac:(rewrite nv_0; lia) F1') as F2.
  destruct (fill_loop eb' mI mI 0%uint63 pos1 adj1 (Zwf_well_founded 0 (gap mI 0%uint63)))
    as [posA adjA] eqn:E2.
  simpl in F2. replace (m + m)%nat with (2 * m)%nat in F2 by lia.
  (* the root *)
  pose proof (root_spec n m ea eb mI Hea Heb Hn Hnb HmI degA n' HnI _ 0%uint63
                (Zwf_well_founded 0 (gap n' 0%uint63)) eq_refl) as Hr.
  set (rI := root_loop degA n' 0%uint63 (Zwf_well_founded 0 (gap n' 0%uint63))) in *.
  (* the traversal *)
  set (mark := (PArray.make n' 0%uint63).[rI <- 1%uint63]).
  set (stk := (PArray.make n' 0%uint63).[0%uint63 <- rI]).
  assert (O : outer n m ea eb (nv rI) [] [nv rI] (fun _ => nv rI) (fun _ => 0%nat)
                mark stk 1%uint63 (PArray.make n' 0%uint63) 0%uint63 0%uint63).
  { split; [|split; [exact Lmk | split; [reflexivity | split; [reflexivity | split;
      [intros i Hi; simpl in Hi; lia | split; [reflexivity | split; [intros []; reflexivity
      | intros u []]]]]]]].
    split; [unfold mark; rewrite alength_set; exact Lmk|].
    split; [unfold stk; rewrite alength_set; exact Lmk|].
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
    - intros v Hv0. simpl. unfold mark. destruct (N.eq_dec v (nv rI)) as [-> | Ne].
      + rewrite rd_set_same by (rewrite ?Lmk; reflexivity || lia). rewrite nv_1. split; [auto | lia].
      + rewrite rd_set_other by lia. rewrite rd_make, nv_0. split; [lia | intros [E | []]; congruence].
    - simpl. constructor; [simpl; tauto | constructor].
    - intros x [<- | []]. exact Hr.
    - reflexivity.
    - intros i Hi. simpl in Hi. replace i with 0%nat by lia. unfold stk.
      rewrite rd_set_same by (rewrite ?Lmk; reflexivity || lia). reflexivity.
    - reflexivity.
    - intros v [<- | []] Hne. contradiction.
    - intros i Hi. simpl in Hi. lia.
    - intros i Hi. simpl in Hi. replace i with 0%nat by lia. simpl. apply anc_refl. }
  destruct (dfs_spec n m ea eb ea' eb' mI Hea Heb Hn Hnb AeA AeB VA VB HmI (nv rI) adjA posA degA
              Hr F2 Hdeg n' HnI Vt _ 0%uint63 [] [nv rI] (fun _ => nv rI) (fun _ => 0%nat)
              mark stk 1%uint63 (PArray.make n' 0%uint63) 0%uint63
              (Zwf_well_founded 0 (gap n' 0%uint63)) eq_refl O)
    as (ord & par & pe & Fn & Ll & EL & Elv).
  destruct (dfs_loop ea' eb' adjA degA posA n' mI 0%uint63 mark stk 1%uint63 (PArray.make n' 0%uint63) 0%uint63
              (Zwf_well_founded 0 (gap n' 0%uint63))) as [lv L] eqn:E3.
  simpl in Ll, EL, Elv.
  set (Lv := leaves ea eb ord) in *.
  destruct Fn as (Nd & Hall & Hlen & Hr0 & Hpr & Hpar & Hchain).
  assert (HLb : (List.length Lv <= S m)%nat).
  { rewrite <- Hlen. unfold Lv, leaves. clear. induction ord as [| x l IH]; simpl; [lia|].
    destruct (Nat.eqb _ 1); simpl; lia. }
  assert (HaI : nv (L >> 1)%uint63 = N.of_nat (List.length Lv / 2)).
  { rewrite nv_lsr1, EL. rewrite Nat2N.inj_div. reflexivity. }
  assert (HcI : nv (L - (L >> 1))%uint63 = N.of_nat (List.length Lv - List.length Lv / 2)).
  { rewrite nv_sub; rewrite HaI, EL; [|pose proof (Nat.Div0.div_le_upper_bound (List.length Lv) 2 (List.length Lv)); lia].
    rewrite Nat2N.inj_sub. reflexivity. }
  assert (Lc : nv (PArray.length (PArray.make (L - (L >> 1))%uint63 0%uint63)) = nv (L - (L >> 1))%uint63)
    by (rewrite alength_make; [reflexivity | lia]).
  destruct (out_spec Lv lv (L >> 1)%uint63 (L - (L >> 1))%uint63 ltac:(lia) Elv HaI HcI
              _ 0%uint63 (PArray.make (L - (L >> 1))%uint63 0%uint63) (PArray.make (L - (L >> 1))%uint63 0%uint63)
              (Zwf_well_founded 0 (gap (L - (L >> 1))%uint63 0%uint63)) eq_refl ltac:(rewrite nv_0; lia) Lc Lc
              ltac:(intros k Hk; rewrite nv_0 in Hk; lia))
    as [Ox Oy].
  exists (firstn (List.length Lv - List.length Lv / 2) Lv, skipn (List.length Lv / 2) Lv).
  split.
  - split; apply arr_repr; assumption.
  - apply (tree_spec n m ea eb ord par pe (nv rI) Hea Heb Hn Hm1 Nd Hall Hlen Hr0 Hpr Hpar Hchain h Hv).
Qed.

Definition kingpin_escape_correct :
  forall (n h : N) (ea eb : list N) (n' h' : uint) (ea' eb' : array uint),
  valid_input n h ea eb ->
  repr n' n -> repr h' h -> repr ea' ea -> repr eb' eb ->
  exists o : list N * list N,
    repr (kingpin_escape n' h' ea' eb') o /\ kingpin_escape_spec n h ea eb o
  := kingpin_impl_correct.
