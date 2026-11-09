(* Correctness proofs for stringmultimatching_implem.v. *)
(* Implementation of stringmultimatching (stringmultimatching.spec):
   Aho-Corasick, one automaton for all the patterns.

   Code.
   - [sums]: total length P and maximum length L of the patterns.
   - The trie is built LEVEL BY LEVEL ([rounds] / [round_loop]): at depth d
     every pattern still longer than d (the active list, compacted in place
     in one array) moves one character down from its current node,
     creating the child if absent.  Nodes are therefore numbered in
     breadth-first order (depth non-decreasing with the index).  Sparse
     transitions: the children of a node are a linked list (first child
     tfc, next sibling tns, edge character tchr), all flat [array int]s of
     size P+1; node 0 is the root.
   - [plist_loop]: the patterns ending at each node, as a linked list
     (fp / np, pattern numbers plus one, 0 ends a list) -- duplicate
     patterns share a node.
   - [fail_loop]: failure and output (dictionary-suffix) links, nodes in
     index order (= breadth-first order), by the failure walk [walk].
   - [scan]: the single left-to-right pass over the text, read through
     PrimString.get; at each position the output chain is walked and every
     pattern of every node on it is reported.  [scan] is generic in the
     action; it runs twice: [f_cnt] counts the occurrences of each pattern,
     then the rows are allocated at their exact sizes ([alloc_loop]) and
     [f_fill] writes the positions in place.  All arrays threaded linearly.
   Termination: every loop recurses on an erased [Acc (Zwf 0)] proof of a
   Z measure (an index gap, or the node / list element itself, which
   decreases along tns, np, failure and output links -- checked at run
   time, proven never to fail).

   Proof.  A ghost word W v for every node; [TrieInv] (prefix-closed,
   injective, depth monotone in the index, child lists = children);
   [FailOK] / [OutOK] for the links; [Longest]: the state after a text
   prefix X is the deepest node whose word is a suffix of X; the per-pattern
   lists of reported positions are abstracted by a relation R in
   [scan_spec], instantiated by [Rcnt] and [Rfill]. *)

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require PrimString String Ascii.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Require Export stringmultimatching_implem.
Open Scope uint63_scope.
Open Scope array_scope.


(* ================================================================== *)
(* Prop side                                                           *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* Uint63 / PArray plumbing                                            *)
(* ------------------------------------------------------------------ *)

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma max_length_val : (φ PArray.max_length) = 4194303%Z.
Proof. reflexivity. Qed.

Lemma alength_bound : forall A (t : array A), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros A t. pose proof (leb_length A t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

Lemma alength_make : forall A (n : int) (b : A),
  ((φ n) <= 4194303)%Z -> PArray.length (PArray.make n b) = n.
Proof.
  intros A n b H. rewrite length_make.
  replace (n <=? PArray.max_length) with true; [reflexivity|].
  symmetry. rewrite leb_spec, max_length_val. exact H.
Qed.

Lemma alength_set : forall (t : array int) (i : int) (b : int),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set int t i b). Qed.

Lemma aget_set_same : forall (t : array int) (i : int) (b : int),
  ((φ i) < (φ (PArray.length t)))%Z -> t.[i <- b].[i] = b.
Proof. intros t i b H. apply (get_set_same int t i b). apply ltb_spec. exact H. Qed.

Lemma aget_set_other : forall (t : array int) (i j : int) (b : int),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other int t i j b H). Qed.

Lemma aget_make : forall (n i b : int), (PArray.make n b).[i] = b.
Proof. intros n i b. exact (get_make int b n i). Qed.

Lemma amake_len : forall (n b : int), ((φ n) <= 4194303)%Z ->
  PArray.length (PArray.make n b) = n.
Proof. intros n b H. exact (alength_make int n b H). Qed.

Lemma int_eq_dec : forall x y : int, {x = y} + {x <> y}.
Proof.
  intros x y. destruct (x =? y) eqn:E.
  - left. apply eqb_spec. exact E.
  - right. intro F. apply eqb_spec in F. congruence.
Defined.

Lemma neq_phi : forall x y : int, x <> y -> (φ x) <> (φ y).
Proof. intros x y H E. apply H. apply to_Z_inj. exact E. Qed.

Lemma eqb_true : forall x y : int, (x =? y) = true -> x = y.
Proof. intros x y H. apply eqb_spec. exact H. Qed.

Lemma eqb_false : forall x y : int, (x =? y) = false -> x <> y.
Proof. intros x y H E. subst. rewrite eqb_refl in H. discriminate. Qed.

Lemma ltb_true : forall x y : int, (x <? y) = true -> ((φ x) < (φ y))%Z.
Proof. intros x y H. apply ltb_spec. exact H. Qed.

Lemma ltb_false : forall x y : int, (x <? y) = false -> ((φ y) <= (φ x))%Z.
Proof.
  intros x y H. rewrite <- Bool.not_true_iff_false, ltb_spec in H. lia.
Qed.

Lemma phi_bnd : forall x : int, (0 <= (φ x) < wB)%Z.
Proof. exact to_Z_bounded. Qed.

Lemma phi0 : (φ 0) = 0%Z.
Proof. reflexivity. Qed.

Lemma phi1 : (φ 1) = 1%Z.
Proof. reflexivity. Qed.

Lemma phi_of_Z : forall z : Z, (0 <= z < wB)%Z -> (φ (of_Z z)) = z.
Proof. intros z H. rewrite of_Z_spec. apply Z.mod_small. exact H. Qed.

Lemma phi_add1 : forall x : int, ((φ x) + 1 < wB)%Z -> (φ (x + 1)) = ((φ x) + 1)%Z.
Proof. intros x H. sia. Qed.

Lemma phi_inj : forall x y : int, (φ x) = (φ y) -> x = y.
Proof. exact to_Z_inj. Qed.

(* ------------------------------------------------------------------ *)
(* Linked lists through an array of next pointers                      *)
(* ------------------------------------------------------------------ *)

Inductive Reach (ns : array int) : int -> int -> Prop :=
| R_here : forall a, a <> 0 -> Reach ns a a
| R_next : forall a b, a <> 0 -> Reach ns ns.[a] b -> Reach ns a b.

Lemma Reach_nz : forall ns a b, Reach ns a b -> a <> 0 /\ b <> 0.
Proof.
  intros ns a b H. induction H as [a Ha | a b Ha H [_ IH]]; auto.
Qed.

Lemma Reach_0 : forall ns b, ~ Reach ns 0 b.
Proof. intros ns b H. apply Reach_nz in H. tauto. Qed.

Lemma Reach_cons : forall ns a b, a <> 0 ->
  (Reach ns a b <-> b = a \/ Reach ns ns.[a] b).
Proof.
  intros ns a b Ha. split.
  - intros H. inversion H; subst; auto.
  - intros [E | H]; [subst; constructor; exact Ha | apply R_next; auto].
Qed.

Lemma Reach_le : forall (ns : array int) (K : Z),
  (forall x, (0 < (φ x) <= K)%Z -> ((φ (ns.[x])) < (φ x))%Z) ->
  forall a b, ((φ a) <= K)%Z -> Reach ns a b -> ((φ b) <= (φ a))%Z.
Proof.
  intros ns K HK a b Ha H. induction H as [a Ha0 | a b Ha0 H IH]; [lia|].
  assert (0 < (φ a))%Z by (pose proof (phi_bnd a); pose proof (neq_phi _ _ Ha0); rewrite phi0 in *; lia).
  pose proof (HK a ltac:(lia)). specialize (IH ltac:(lia)). lia.
Qed.

Lemma Reach_frame : forall ns a e y b,
  (forall x, Reach ns a x -> x <> e) ->
  (Reach ns.[e <- y] a b <-> Reach ns a b).
Proof.
  intros ns a e y b Hx. split.
  - intros H. induction H as [a Ha | a b Ha H IH].
    + constructor. exact Ha.
    + assert (Hae : a <> e) by (apply Hx; constructor; exact Ha).
      assert (E : ns.[e <- y].[a] = ns.[a]) by (apply aget_set_other; intro F; apply Hae; symmetry; exact F).
      rewrite E in H, IH.
      apply R_next; [exact Ha|]. apply IH.
      intros x Hr. apply Hx. apply R_next; assumption.
  - intros H. induction H as [a Ha | a b Ha H IH].
    + constructor. exact Ha.
    + assert (Hae : a <> e) by (apply Hx; constructor; exact Ha).
      apply R_next; [exact Ha|].
      assert (E : ns.[e <- y].[a] = ns.[a]) by (apply aget_set_other; intro F; apply Hae; symmetry; exact F).
      rewrite E.
      apply IH. intros x Hr. apply Hx. apply R_next; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Suffixes                                                            *)
(* ------------------------------------------------------------------ *)

Definition suffix (y X : list Z) : Prop := exists z, X = z ++ y.

Lemma suffix_skipn : forall y X, suffix y X <->
  (List.length y <= List.length X)%nat /\ skipn (List.length X - List.length y) X = y.
Proof.
  intros y X. split.
  - intros [z ->]. rewrite length_app.
    replace (List.length z + List.length y - List.length y)%nat with (List.length z) by lia.
    split; [lia|]. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
  - intros [Hl Hs]. exists (firstn (List.length X - List.length y) X).
    rewrite <- Hs at 2. symmetry. apply firstn_skipn.
Qed.

Lemma suffix_length : forall y X, suffix y X -> (List.length y <= List.length X)%nat.
Proof. intros y X [z ->]. rewrite length_app. lia. Qed.

Lemma suffix_refl : forall X, suffix X X.
Proof. intros X. exists []. reflexivity. Qed.

Lemma suffix_nil : forall X, suffix [] X.
Proof. intros X. exists X. rewrite app_nil_r. reflexivity. Qed.

Lemma suffix_trans : forall a b c, suffix a b -> suffix b c -> suffix a c.
Proof.
  intros a b c [z1 ->] [z2 ->]. exists (z2 ++ z1). rewrite app_assoc. reflexivity.
Qed.

Lemma suffix_both : forall a b X, suffix a X -> suffix b X ->
  (List.length a <= List.length b)%nat -> suffix a b.
Proof.
  intros a b X Ha Hb Hl.
  apply suffix_skipn in Ha as [Ha1 Ha2]. apply suffix_skipn in Hb as [Hb1 Hb2].
  apply suffix_skipn. split; [exact Hl|].
  set (la := List.length a) in *. set (lb := List.length b) in *.
  set (lx := List.length X) in *.
  rewrite <- Hb2, skipn_skipn. rewrite <- Ha2. f_equal. lia.
Qed.

Lemma suffix_eq : forall a b X, suffix a X -> suffix b X ->
  List.length a = List.length b -> a = b.
Proof.
  intros a b X Ha Hb Hl.
  apply suffix_skipn in Ha as [_ Ha2]. apply suffix_skipn in Hb as [_ Hb2].
  rewrite Hl in Ha2. congruence.
Qed.

Lemma suffix_snoc : forall y a X c,
  suffix (y ++ [a]) (X ++ [c]) <-> a = c /\ suffix y X.
Proof.
  intros y a X c. split.
  - intros [z Hz]. rewrite app_assoc in Hz. apply app_inj_tail in Hz as [H1 H2].
    split; [symmetry; exact H2 | exists z; exact H1].
  - intros [-> [z ->]]. exists z. rewrite app_assoc. reflexivity.
Qed.

Lemma suffix_snoc_cases : forall w X c, suffix w (X ++ [c]) ->
  w = [] \/ exists y, w = y ++ [c] /\ suffix y X.
Proof.
  intros w X c H. destruct (list_eq_dec Z.eq_dec w []) as [-> | Hn]; [left; reflexivity|].
  destruct (exists_last Hn) as (y & a & ->).
  right. apply suffix_snoc in H as [-> H]. exists y. split; [reflexivity | exact H].
Qed.

(* ------------------------------------------------------------------ *)
(* The trie invariant                                                  *)
(* ------------------------------------------------------------------ *)

(* W v is the word of node v, a ghost. *)
Definition IsNode (t : trie) (W : int -> list Z) (y : list Z) : Prop :=
  exists z, ((φ z) < (φ (tn t)))%Z /\ W z = y.

Record TrieInv (t : trie) (cap : Z) (W : int -> list Z) : Prop := {
  ti_lchr : (φ (PArray.length (tchr t))) = cap;
  ti_lpar : (φ (PArray.length (tpar t))) = cap;
  ti_lfc : (φ (PArray.length (tfc t))) = cap;
  ti_lns : (φ (PArray.length (tns t))) = cap;
  ti_ldep : (φ (PArray.length (tdep t))) = cap;
  ti_n : (1 <= (φ (tn t)) <= cap)%Z;
  ti_root : W 0 = [];
  ti_par : forall v, (0 < (φ v) < (φ (tn t)))%Z ->
     ((φ ((tpar t).[v])) < (φ v))%Z /\ W v = W ((tpar t).[v]) ++ [(φ ((tchr t).[v]))];
  ti_dep : forall v, ((φ v) < (φ (tn t)))%Z ->
     (φ ((tdep t).[v])) = Z.of_nat (List.length (W v));
  ti_inj : forall u v, ((φ u) < (φ (tn t)))%Z -> ((φ v) < (φ (tn t)))%Z -> W u = W v -> u = v;
  ti_mono : forall u v, ((φ u) < (φ (tn t)))%Z -> ((φ v) < (φ (tn t)))%Z -> ((φ u) <= (φ v))%Z ->
     (List.length (W u) <= List.length (W v))%nat;
  ti_ns : forall v, (0 < (φ v) < (φ (tn t)))%Z -> ((φ ((tns t).[v])) < (φ v))%Z;
  ti_ch : forall u, ((φ u) < (φ (tn t)))%Z -> forall v,
     Reach (tns t) ((tfc t).[u]) v <-> ((0 < (φ v) < (φ (tn t)))%Z /\ (tpar t).[v] = u);
  ti_fresh : forall u, ((φ (tn t)) <= (φ u) < cap)%Z -> (tfc t).[u] = 0;
}.

Lemma pos_of_nz : forall v : int, v <> 0 -> (0 < (φ v))%Z.
Proof.
  intros v H. pose proof (phi_bnd v). pose proof (neq_phi _ _ H). rewrite phi0 in *. lia.
Qed.

Lemma nz_of_pos : forall v : int, (0 < (φ v))%Z -> v <> 0.
Proof. intros v H E. subst. rewrite phi0 in H. lia. Qed.

Lemma ti_cap : forall t cap W, TrieInv t cap W -> (cap <= 4194303)%Z.
Proof.
  intros t cap W Ht. rewrite <- (ti_lchr _ _ _ Ht). exact (alength_bound int (tchr t)).
Qed.

Lemma ti_word_nz : forall t cap W v, TrieInv t cap W -> (0 < (φ v) < (φ (tn t)))%Z ->
  W v <> [].
Proof.
  intros t cap W v Ht Hv E. destruct (ti_par _ _ _ Ht v Hv) as [_ E2].
  rewrite E in E2. destruct (W (tpar t).[v]); discriminate.
Qed.

Lemma ti_nil : forall t cap W v, TrieInv t cap W -> ((φ v) < (φ (tn t)))%Z ->
  W v = [] -> v = 0.
Proof.
  intros t cap W v Ht Hv E. destruct (int_eq_dec v 0) as [|Hn]; [assumption|].
  exfalso. apply (ti_word_nz t cap W v Ht); [|exact E].
  split; [apply pos_of_nz; exact Hn | exact Hv].
Qed.

Lemma ti_lt : forall t cap W u v, TrieInv t cap W ->
  ((φ u) < (φ (tn t)))%Z -> ((φ v) < (φ (tn t)))%Z ->
  (List.length (W u) < List.length (W v))%nat -> ((φ u) < (φ v))%Z.
Proof.
  intros t cap W u v Ht Hu Hv Hl.
  destruct (Z_lt_le_dec (φ u) (φ v)) as [|H]; [assumption|].
  pose proof (ti_mono _ _ _ Ht v u Hv Hu H). lia.
Qed.

Lemma ti_depth_le : forall t cap W, TrieInv t cap W ->
  forall v, ((φ v) < (φ (tn t)))%Z -> (Z.of_nat (List.length (W v)) <= (φ v))%Z.
Proof.
  intros t cap W Ht.
  assert (forall z v, (φ v) = z -> ((φ v) < (φ (tn t)))%Z -> (Z.of_nat (List.length (W v)) <= (φ v))%Z);
    [|intros v; apply (H (φ v) v eq_refl)].
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros v Hz Hv. destruct (int_eq_dec v 0) as [-> | Hn].
  - rewrite (ti_root _ _ _ Ht). simpl. lia.
  - pose proof (pos_of_nz v Hn) as Hp.
    destruct (ti_par _ _ _ Ht v ltac:(lia)) as [Hpv Ew].
    pose proof (phi_bnd ((tpar t).[v])).
    assert (IH' := IH (φ ((tpar t).[v])) ltac:(unfold Zwf; lia) _ eq_refl ltac:(lia)).
    rewrite Ew, length_app. simpl. lia.
Qed.

Lemma isnode_prefix : forall t cap W y a, TrieInv t cap W ->
  IsNode t W (y ++ [a]) -> IsNode t W y.
Proof.
  intros t cap W y a Ht [z [Hz Ew]].
  assert (Hz0 : z <> 0).
  { intro E. subst. rewrite (ti_root _ _ _ Ht) in Ew. destruct y; discriminate. }
  pose proof (pos_of_nz z Hz0).
  destruct (ti_par _ _ _ Ht z ltac:(lia)) as [Hp Ew2].
  rewrite Ew in Ew2. apply app_inj_tail in Ew2 as [E1 _].
  exists ((tpar t).[z]). split; [lia | symmetry; exact E1].
Qed.

(* ------------------------------------------------------------------ *)
(* lookup                                                              *)
(* ------------------------------------------------------------------ *)

Lemma lookup_from_eq : forall chr ns c v H,
  lookup_from chr ns c v H =
  match bdec (v =? 0) with
  | left _ => 0
  | right _ =>
      if chr.[v] =? c then v else
      let nx := ns.[v] in
      match bdec (nx <? v) with
      | left Hn => lookup_from chr ns c nx (Acc_inv H (dec_lt v nx Hn))
      | right _ => 0
      end
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma lookup_from_spec : forall chr ns c v H,
  (forall x, Reach ns v x -> ((φ (ns.[x])) < (φ x))%Z) ->
  (lookup_from chr ns c v H <> 0 ->
     Reach ns v (lookup_from chr ns c v H) /\ chr.[lookup_from chr ns c v H] = c) /\
  (lookup_from chr ns c v H = 0 -> forall x, Reach ns v x -> chr.[x] <> c).
Proof.
  intros chr ns c.
  assert (G : forall z v H, (φ v) = z ->
    (forall x, Reach ns v x -> ((φ (ns.[x])) < (φ x))%Z) ->
    (lookup_from chr ns c v H <> 0 ->
       Reach ns v (lookup_from chr ns c v H) /\ chr.[lookup_from chr ns c v H] = c) /\
    (lookup_from chr ns c v H = 0 -> forall x, Reach ns v x -> chr.[x] <> c));
    [|intros v H; exact (G _ v H eq_refl)].
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros v H Hz Hd. rewrite lookup_from_eq.
  destruct (bdec (v =? 0)) as [E | E].
  - apply eqb_true in E. subst v. split; [tauto|].
    intros _ x Hr. exfalso. exact (Reach_0 _ _ Hr).
  - apply eqb_false in E.
    destruct (chr.[v] =? c) eqn:Ec.
    + apply eqb_true in Ec. split; [intros _; split; [constructor; exact E | exact Ec]|].
      intros F. contradiction.
    + apply eqb_false in Ec. cbv zeta.
      destruct (bdec (ns.[v] <? v)) as [Hn | Hn].
      * pose proof (ltb_true _ _ Hn) as Hn'.
        assert (Hd' : forall x, Reach ns ns.[v] x -> ((φ (ns.[x])) < (φ x))%Z)
          by (intros x Hr; apply Hd; apply R_next; assumption).
        destruct (IH (φ (ns.[v])) ltac:(rewrite <- Hz; apply dec_lt; exact Hn)
                    (ns.[v]) (Acc_inv H (dec_lt v ns.[v] Hn)) eq_refl Hd') as [IH1 IH2].
        split.
        -- intros Hy. destruct (IH1 Hy) as [Hr Hc]. split; [apply R_next; assumption | exact Hc].
        -- intros Hy x Hr. apply (Reach_cons ns v x E) in Hr as [-> | Hr]; [exact Ec|].
           exact (IH2 Hy x Hr).
      * exfalso. pose proof (ltb_false _ _ Hn).
        pose proof (Hd v ltac:(constructor; exact E)). lia.
Qed.

Lemma lookup_spec : forall t cap W u c, TrieInv t cap W -> ((φ u) < (φ (tn t)))%Z ->
  (lookup t u c <> 0 ->
     (0 < (φ (lookup t u c)) < (φ (tn t)))%Z /\ W (lookup t u c) = W u ++ [(φ c)]) /\
  (lookup t u c = 0 -> ~ IsNode t W (W u ++ [(φ c)])).
Proof.
  intros t cap W u c Ht Hu. unfold lookup.
  set (v0 := (tfc t).[u]).
  assert (Hd : forall x, Reach (tns t) v0 x -> ((φ ((tns t).[x])) < (φ x))%Z).
  { intros x Hr. apply (ti_ch _ _ _ Ht u Hu x) in Hr as [Hx _]. apply (ti_ns _ _ _ Ht). exact Hx. }
  destruct (lookup_from_spec (tchr t) (tns t) c v0 (Zwf_well_founded 0 (φ v0)) Hd) as [H1 H2].
  set (y := lookup_from (tchr t) (tns t) c v0 (Zwf_well_founded 0 (φ v0))) in *.
  split.
  - intros Hy. destruct (H1 Hy) as [Hr Hc].
    apply (ti_ch _ _ _ Ht u Hu y) in Hr as [Hy' Hp].
    split; [exact Hy'|]. destruct (ti_par _ _ _ Ht y Hy') as [_ Ew].
    rewrite Ew, Hp, Hc. reflexivity.
  - intros Hy [z [Hz Ew]].
    assert (Hz0 : z <> 0).
    { intro E. subst. rewrite (ti_root _ _ _ Ht) in Ew. destruct (W u); discriminate. }
    pose proof (pos_of_nz z Hz0).
    destruct (ti_par _ _ _ Ht z ltac:(lia)) as [Hp Ew2].
    rewrite Ew in Ew2. apply app_inj_tail in Ew2 as [E1 E2].
    pose proof (phi_bnd ((tpar t).[z])).
    assert (Epar : (tpar t).[z] = u)
      by (apply (ti_inj _ _ _ Ht); [lia | exact Hu | symmetry; exact E1]).
    apply (H2 Hy z).
    + apply (ti_ch _ _ _ Ht u Hu z). split; [lia | exact Epar].
    + apply phi_inj. symmetry. exact E2.
Qed.

Lemma ilen_bound : forall (t : array int), ((φ (PArray.length t)) <= 4194303)%Z.
Proof. intros t. exact (alength_bound int t). Qed.

(* ------------------------------------------------------------------ *)
(* add_child                                                           *)
(* ------------------------------------------------------------------ *)

Lemma add_child_spec : forall t cap W u c, TrieInv t cap W -> ((φ u) < (φ (tn t)))%Z ->
  ((φ (tn t)) < cap)%Z ->
  (forall x, ((φ x) < (φ (tn t)))%Z -> (List.length (W x) <= S (List.length (W u)))%nat) ->
  exists W', TrieInv (fst (add_child t u c)) cap W' /\
    (forall x, ((φ x) < (φ (tn t)))%Z -> W' x = W x) /\
    ((φ (tn (fst (add_child t u c)))) = (φ (tn t)) \/
     (φ (tn (fst (add_child t u c)))) = (φ (tn t)) + 1)%Z /\
    ((φ (snd (add_child t u c))) < (φ (tn (fst (add_child t u c)))))%Z /\
    W' (snd (add_child t u c)) = W u ++ [(φ c)] /\
    (forall x, ((φ x) < (φ (tn (fst (add_child t u c)))))%Z ->
       ((φ x) < (φ (tn t)))%Z \/ W' x = W u ++ [(φ c)]).
Proof.
  intros t cap W u c Ht Hu Hcap Hdep.
  destruct (lookup_spec t cap W u c Ht Hu) as [L1 L2].
  pose proof (ti_cap _ _ _ Ht) as Hcap4.
  unfold add_child. destruct (lookup t u c =? 0) eqn:E.
  2:{ apply eqb_false in E. destruct (L1 E) as [Hy Ew].
      exists W. simpl. split; [exact Ht|]. split; [reflexivity|].
      split; [left; reflexivity|]. split; [lia|]. split; [exact Ew|].
      intros x Hx. left. exact Hx. }
  apply eqb_true in E. specialize (L2 E).
  pose proof (ti_n _ _ _ Ht) as Hn.
  set (n := tn t) in *.
  assert (Hn1 : (φ (n + 1)) = ((φ n) + 1)%Z) by (apply phi_add1; rewrite wB_val; lia).
  set (Wn := W u ++ [(φ c)]).
  set (W' := fun x => if x =? n then Wn else W x).
  assert (W'n : W' n = Wn) by (unfold W'; rewrite eqb_refl; reflexivity).
  assert (W'o : forall x, x <> n -> W' x = W x)
    by (intros x Hx; unfold W'; destruct (x =? n) eqn:Ex; [apply eqb_true in Ex; contradiction | reflexivity]).
  assert (Hlt_n : forall x, ((φ x) < (φ n))%Z -> x <> n) by (intros x Hx F; subst; lia).
  assert (Hun : u <> n) by (apply Hlt_n; exact Hu).
  exists W'. simpl.
  assert (Hlfc : (φ (PArray.length (tfc t))) = cap) by exact (ti_lfc _ _ _ Ht).
  assert (Hlns : (φ (PArray.length (tns t))) = cap) by exact (ti_lns _ _ _ Ht).
  assert (Hlpar : (φ (PArray.length (tpar t))) = cap) by exact (ti_lpar _ _ _ Ht).
  assert (Hlchr : (φ (PArray.length (tchr t))) = cap) by exact (ti_lchr _ _ _ Ht).
  assert (Hldep : (φ (PArray.length (tdep t))) = cap) by exact (ti_ldep _ _ _ Ht).
  (* children of an old node are old nodes *)
  assert (Hold : forall u', ((φ u') < (φ n))%Z -> forall x, Reach (tns t) ((tfc t).[u']) x -> x <> n).
  { intros u' Hu' x Hr. apply (ti_ch _ _ _ Ht u' Hu' x) in Hr as [Hx _]. apply Hlt_n. lia. }
  split; [constructor; simpl | ].
  - rewrite alength_set. exact Hlchr.
  - rewrite alength_set. exact Hlpar.
  - rewrite alength_set. exact Hlfc.
  - rewrite alength_set. exact Hlns.
  - rewrite alength_set. exact Hldep.
  - lia.
  - rewrite W'o by (intro F; rewrite <- F, phi0 in Hn; lia).
    exact (ti_root _ _ _ Ht).
  - intros v Hv. rewrite Hn1 in Hv. destruct (int_eq_dec v n) as [-> | Hvn].
    + rewrite aget_set_same by lia. rewrite aget_set_same by lia.
      rewrite W'n, W'o by exact Hun. split; [exact Hu | reflexivity].
    + rewrite aget_set_other by (intro F; apply Hvn; symmetry; exact F).
      rewrite aget_set_other by (intro F; apply Hvn; symmetry; exact F).
      assert (Hv' : (0 < (φ v) < (φ n))%Z) by (pose proof (neq_phi _ _ Hvn); lia).
      destruct (ti_par _ _ _ Ht v Hv') as [Hp Ew].
      rewrite W'o by exact Hvn. rewrite W'o by (apply Hlt_n; lia).
      split; [exact Hp | exact Ew].
  - intros v Hv. rewrite Hn1 in Hv. destruct (int_eq_dec v n) as [-> | Hvn].
    + rewrite aget_set_same by lia. rewrite W'n.
      unfold Wn. rewrite length_app. simpl.
      pose proof (ti_depth_le _ _ _ Ht u Hu).
      assert (Hd : (φ ((tdep t).[u])) = Z.of_nat (List.length (W u))) by exact (ti_dep _ _ _ Ht u Hu).
      rewrite phi_add1 by (rewrite Hd, wB_val; lia). rewrite Hd. lia.
    + rewrite aget_set_other by (intro F; apply Hvn; symmetry; exact F).
      rewrite W'o by exact Hvn. apply (ti_dep _ _ _ Ht). pose proof (neq_phi _ _ Hvn). lia.
  - intros x y Hx Hy Exy. rewrite Hn1 in Hx, Hy.
    destruct (int_eq_dec x n) as [-> | Hxn]; destruct (int_eq_dec y n) as [-> | Hyn];
      [reflexivity | | | ].
    + exfalso. rewrite W'n, W'o in Exy by exact Hyn. apply L2.
      exists y. split; [pose proof (neq_phi _ _ Hyn); lia | symmetry; exact Exy].
    + exfalso. rewrite W'n, W'o in Exy by exact Hxn. apply L2.
      exists x. split; [pose proof (neq_phi _ _ Hxn); lia | exact Exy].
    + rewrite W'o in Exy by exact Hxn. rewrite W'o in Exy by exact Hyn.
      apply (ti_inj _ _ _ Ht); [pose proof (neq_phi _ _ Hxn) | pose proof (neq_phi _ _ Hyn) | ]; [lia|lia|exact Exy].
  - intros x y Hx Hy Hxy. rewrite Hn1 in Hx, Hy.
    destruct (int_eq_dec y n) as [-> | Hyn].
    + rewrite W'n. unfold Wn. rewrite length_app. simpl.
      destruct (int_eq_dec x n) as [-> | Hxn]; [rewrite W'n; unfold Wn; rewrite length_app; simpl; lia|].
      rewrite W'o by exact Hxn. pose proof (Hdep x ltac:(pose proof (neq_phi _ _ Hxn); lia)). lia.
    + destruct (int_eq_dec x n) as [-> | Hxn]; [exfalso; pose proof (neq_phi _ _ Hyn); lia|].
      rewrite W'o by exact Hxn. rewrite W'o by exact Hyn.
      apply (ti_mono _ _ _ Ht); [pose proof (neq_phi _ _ Hxn) | pose proof (neq_phi _ _ Hyn) | ]; lia.
  - intros v Hv. rewrite Hn1 in Hv. destruct (int_eq_dec v n) as [-> | Hvn].
    + rewrite aget_set_same by lia.
      destruct (int_eq_dec ((tfc t).[u]) 0) as [E0 | E0]; [rewrite E0, phi0; lia|].
      assert (Hr : Reach (tns t) ((tfc t).[u]) ((tfc t).[u])) by (constructor; exact E0).
      apply (ti_ch _ _ _ Ht u Hu) in Hr. lia.
    + rewrite aget_set_other by (intro F; apply Hvn; symmetry; exact F).
      apply (ti_ns _ _ _ Ht). pose proof (neq_phi _ _ Hvn). lia.
  - intros u' Hu' v. rewrite Hn1 in Hu' |- *.
    destruct (int_eq_dec u' u) as [-> | Hu'u].
    + rewrite aget_set_same by lia.
      assert (Hn0 : n <> 0) by (apply nz_of_pos; lia).
      rewrite (Reach_cons _ n v Hn0).
      rewrite aget_set_same by lia.
      rewrite (Reach_frame (tns t) ((tfc t).[u]) n ((tfc t).[u]) v (Hold u Hu)).
      rewrite (ti_ch _ _ _ Ht u Hu v).
      destruct (int_eq_dec v n) as [-> | Hvn].
      * rewrite aget_set_same by lia. split; [intros _; split; [lia | reflexivity] | intros _; left; reflexivity].
      * rewrite aget_set_other by (intro F; apply Hvn; symmetry; exact F).
        pose proof (neq_phi _ _ Hvn). split.
        -- intros [F | [H1 H2]]; [contradiction | split; [lia | exact H2]].
        -- intros [H1 H2]. right. split; [lia | exact H2].
    + rewrite aget_set_other by (intro F; apply Hu'u; symmetry; exact F).
      destruct (int_eq_dec u' n) as [-> | Hu'n].
      * rewrite (ti_fresh _ _ _ Ht n ltac:(lia)). split; [intros F; exfalso; exact (Reach_0 _ _ F)|].
        intros [Hv Hp]. exfalso. destruct (int_eq_dec v n) as [-> | Hvn].
        -- rewrite aget_set_same in Hp by lia. exact (Hun Hp).
        -- rewrite aget_set_other in Hp by (intro F; apply Hvn; symmetry; exact F).
           pose proof (neq_phi _ _ Hvn).
           destruct (ti_par _ _ _ Ht v ltac:(lia)) as [Hpv _]. rewrite Hp in Hpv. lia.
      * assert (Hu'' : ((φ u') < (φ n))%Z) by (pose proof (neq_phi _ _ Hu'n); lia).
        rewrite (Reach_frame (tns t) ((tfc t).[u']) n ((tfc t).[u]) v (Hold u' Hu'')).
        rewrite (ti_ch _ _ _ Ht u' Hu'' v).
        destruct (int_eq_dec v n) as [-> | Hvn].
        -- rewrite aget_set_same by lia. split.
           ++ intros [H1 H2]. lia.
           ++ intros [_ H2]. exfalso. exact (Hu'u (eq_sym H2)).
        -- rewrite aget_set_other by (intro F; apply Hvn; symmetry; exact F).
           pose proof (neq_phi _ _ Hvn). split; intros [H1 H2]; split; auto; lia.
  - intros u' Hu'. rewrite Hn1 in Hu'.
    rewrite aget_set_other by (intro F; subst; lia).
    apply (ti_fresh _ _ _ Ht). lia.
  - split; [intros x Hx; apply W'o; apply Hlt_n; exact Hx|].
    split; [right; exact Hn1|].
    split; [rewrite Hn1; lia|].
    split; [exact W'n|].
    intros x Hx. rewrite Hn1 in Hx. destruct (int_eq_dec x n) as [-> | Hxn]; [right; exact W'n|].
    left. pose proof (neq_phi _ _ Hxn). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Words of primitive strings, index lists, sums                       *)
(* ------------------------------------------------------------------ *)

(* the character codes of a primitive string *)
Definition pstr (s : PrimString.string) : list Z :=
  map (fun k => (φ (PrimString.get s (of_Z (Z.of_nat k)))))
      (seq 0 (Z.to_nat (φ (PrimString.length s)))).

Lemma pstr_len : forall s, Z.of_nat (List.length (pstr s)) = (φ (PrimString.length s)).
Proof.
  intros s. unfold pstr. rewrite length_map, length_seq.
  pose proof (phi_bnd (PrimString.length s)). lia.
Qed.

Lemma pstr_nth : forall s (k : int), ((φ k) < (φ (PrimString.length s)))%Z ->
  nth (Z.to_nat (φ k)) (pstr s) 0%Z = (φ (PrimString.get s k)).
Proof.
  intros s k Hk. unfold pstr. pose proof (phi_bnd k).
  set (g := fun k0 : nat => (φ (PrimString.get s (of_Z (Z.of_nat k0))))).
  rewrite nth_indep with (d' := g 0%nat) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. unfold g. simpl. f_equal. f_equal.
  apply phi_inj. rewrite phi_of_Z; lia.
Qed.

Lemma firstn_snoc : forall (l : list Z) d, (d < List.length l)%nat ->
  firstn (S d) l = firstn d l ++ [nth d l 0%Z].
Proof.
  induction l as [| a l IH]; intros d Hd; simpl in Hd; [lia|].
  destruct d as [| d]; [reflexivity|].
  change (firstn (S (S d)) (a :: l)) with (a :: firstn (S d) l).
  rewrite IH by lia. reflexivity.
Qed.

Lemma firstn_snoc_gen : forall {A} (l : list A) d x, (d < List.length l)%nat ->
  firstn (S d) l = firstn d l ++ [nth d l x].
Proof.
  intros A. induction l as [| a l IH]; intros d x Hd; simpl in Hd; [lia|].
  destruct d as [| d]; [reflexivity|].
  change (firstn (S (S d)) (a :: l)) with (a :: firstn (S d) l).
  rewrite (IH d x) by lia. reflexivity.
Qed.

Definition iseq (m : Z) : list int :=
  map (fun k => of_Z (Z.of_nat k)) (seq 0 (Z.to_nat m)).

Lemma iseq_len : forall m, List.length (iseq m) = Z.to_nat m.
Proof. intros m. unfold iseq. rewrite length_map, length_seq. reflexivity. Qed.

Lemma iseq_In : forall m i, (m < wB)%Z -> (In i (iseq m) <-> ((φ i) < m)%Z).
Proof.
  intros m i Hm. unfold iseq. rewrite in_map_iff. split.
  - intros [k [<- Hk]]. apply in_seq in Hk. rewrite phi_of_Z; lia.
  - intros Hi. exists (Z.to_nat (φ i)). pose proof (phi_bnd i). split.
    + apply phi_inj. rewrite phi_of_Z; lia.
    + apply in_seq. lia.
Qed.

Lemma iseq_NoDup : forall m, (m < wB)%Z -> NoDup (iseq m).
Proof.
  intros m Hm. unfold iseq. apply NoDup_map_NoDup_ForallPairs; [|apply seq_NoDup].
  intros a b Ha Hb E. apply in_seq in Ha, Hb.
  assert (E' : (φ (of_Z (Z.of_nat a))) = (φ (of_Z (Z.of_nat b)))) by (rewrite E; reflexivity).
  rewrite !phi_of_Z in E' by lia. lia.
Qed.

Definition zsum (f : int -> Z) (l : list int) : Z :=
  fold_right (fun i a => (f i + a)%Z) 0%Z l.

Lemma zsum_app : forall f l1 l2, zsum f (l1 ++ l2) = (zsum f l1 + zsum f l2)%Z.
Proof. intros f l1 l2. induction l1 as [| a l IH]; simpl; [reflexivity|]. rewrite IH. lia. Qed.

Lemma zsum_ext : forall f g l, (forall i, f i = g i) -> zsum f l = zsum g l.
Proof. intros f g l H. induction l as [| a l IH]; simpl; [reflexivity|]. rewrite IH, H. reflexivity. Qed.

Lemma zsum_le : forall f g l, (forall i, In i l -> (f i <= g i)%Z) -> (zsum f l <= zsum g l)%Z.
Proof.
  intros f g l H. induction l as [| a l IH]; simpl; [lia|].
  pose proof (H a (or_introl eq_refl)). specialize (IH (fun i Hi => H i (or_intror Hi))). lia.
Qed.

Lemma zsum_nonneg : forall f l, (forall i, In i l -> (0 <= f i)%Z) -> (0 <= zsum f l)%Z.
Proof.
  intros f l H. induction l as [| a l IH]; simpl; [lia|].
  pose proof (H a (or_introl eq_refl)). specialize (IH (fun i Hi => H i (or_intror Hi))). lia.
Qed.

Lemma zsum_min_step : forall (p : int -> Z) (d : Z) l,
  zsum (fun i => Z.min (p i) (d + 1)) l =
  (zsum (fun i => Z.min (p i) d) l + Z.of_nat (List.length (filter (fun i => d <? p i)%Z l)))%Z.
Proof.
  intros p d l. induction l as [| a l IH]; simpl; [reflexivity|].
  rewrite IH. destruct (d <? p a)%Z eqn:E; simpl.
  - rewrite Z.ltb_lt in E. lia.
  - rewrite Z.ltb_ge in E. lia.
Qed.

Lemma in_firstn' : forall {A} k (l : list A) x, In x (firstn k l) -> In x l.
Proof. intros A k l x H. rewrite <- (firstn_skipn k l). apply in_or_app. left. exact H. Qed.

Lemma nth_not_in_firstn : forall {A} (l : list A) k x, NoDup l -> (k < List.length l)%nat ->
  ~ In (nth k l x) (firstn k l).
Proof.
  intros A l k x Hl Hk Hin.
  destruct (In_nth _ _ x Hin) as [j [Hj Ej]].
  rewrite length_firstn in Hj. rewrite nth_firstn in Ej.
  destruct (Nat.ltb_spec j k); [|lia].
  rewrite NoDup_nth in Hl. specialize (Hl j k ltac:(lia) Hk (Ej)). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The construction of the trie, level by level                        *)
(* ------------------------------------------------------------------ *)

Lemma round_loop_eq : forall pats d na k st H,
  round_loop pats d na k st H =
  match bdec (k <? na) with
  | left Hk =>
      let act := bact st in
      let i := act.[k] in
      let s := pats.[i] in
      let cur := bcur st in
      let tv := add_child (bt st) cur.[i] (PrimString.get s d) in
      let cur' := cur.[i <- snd tv] in
      let w := bw st in
      if d + 1 <? PrimString.length s then
        round_loop pats d na (k + 1) (mkB act.[w <- i] cur' (w + 1) (fst tv))
          (Acc_inv H (dec_step na k Hk))
      else
        round_loop pats d na (k + 1) (mkB act cur' w (fst tv))
          (Acc_inv H (dec_step na k Hk))
  | right _ => st
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma rounds_eq : forall pats L d st H,
  rounds pats L d st H =
  match bdec (d <? L) with
  | left Hd =>
      let st' := round_loop pats d (bw st) 0 (mkB (bact st) (bcur st) 0 (bt st))
                   (Zwf_well_founded 0 (gap (bw st) 0)) in
      rounds pats L (d + 1) st' (Acc_inv H (dec_step L d Hd))
  | right _ => st
  end.
Proof. intros. destruct H. reflexivity. Qed.

Section Build.
  Variable pats : array PrimString.string.

  Definition m : Z := (φ (PArray.length pats)).
  Definition pw (i : int) : list Z := pstr pats.[i].
  Definition plen (i : int) : Z := (φ (PrimString.length pats.[i])).
  Definition Ld (d : nat) : list int := filter (fun i => Z.of_nat d <? plen i)%Z (iseq m).
  Definition sumd (d : nat) : Z := zsum (fun i => Z.min (plen i) (Z.of_nat d)) (iseq m).
  Definition Ptot : Z := zsum plen (iseq m).
  Definition Lk (d k : nat) : list int :=
    filter (fun i => Z.of_nat (S d) <? plen i)%Z (firstn k (Ld d)).

  Lemma m_bound : (0 <= m <= 4194303)%Z.
  Proof.
    unfold m. pose proof (phi_bnd (PArray.length pats)).
    assert (H0 : ((φ (PArray.length@{Set} pats)) <= 4194303)%Z) by exact (alength_bound _ pats). lia.
  Qed.

  Lemma plen_len : forall i, Z.of_nat (List.length (pw i)) = plen i.
  Proof. intros i. apply pstr_len. Qed.

  Lemma plen_bnd : forall i, (0 <= plen i < wB)%Z.
  Proof. intros i. apply phi_bnd. Qed.

  Lemma Ld_In : forall d i, In i (Ld d) <-> ((φ i) < m)%Z /\ (Z.of_nat d < plen i)%Z.
  Proof.
    intros d i. unfold Ld. rewrite filter_In, iseq_In by (pose proof m_bound; rewrite wB_val; lia).
    rewrite Z.ltb_lt. reflexivity.
  Qed.

  Lemma Ld_NoDup : forall d, NoDup (Ld d).
  Proof.
    intros d. apply NoDup_filter. apply iseq_NoDup. pose proof m_bound; rewrite wB_val; lia.
  Qed.

  Lemma Ld_len : forall d, (Z.of_nat (List.length (Ld d)) <= m)%Z.
  Proof.
    intros d. unfold Ld. pose proof (filter_length_le (fun i => Z.of_nat d <? plen i)%Z (iseq m)).
    rewrite iseq_len in H. pose proof m_bound. lia.
  Qed.

  Lemma sumd_S : forall d, sumd (S d) = (sumd d + Z.of_nat (List.length (Ld d)))%Z.
  Proof.
    intros d. unfold sumd, Ld. rewrite <- zsum_min_step.
    apply zsum_ext. intros i. f_equal. lia.
  Qed.

  Lemma sumd_le : forall d, (sumd d <= Ptot)%Z.
  Proof.
    intros d. unfold sumd, Ptot. apply zsum_le. intros i _. lia.
  Qed.

  Lemma sumd_0 : sumd 0 = 0%Z.
  Proof.
    unfold sumd. rewrite (zsum_ext _ (fun _ => 0%Z)).
    - induction (iseq m) as [| a l IH]; simpl; [reflexivity|]. rewrite IH. reflexivity.
    - intros i. pose proof (plen_bnd i). lia.
  Qed.

  Definition RI (cap : Z) (d k : nat) (st : bstate) : Prop :=
    exists W, TrieInv (bt st) cap W /\
    (forall x, ((φ x) < (φ (tn (bt st))))%Z -> (List.length (W x) <= S d)%nat) /\
    ((φ (tn (bt st))) <= 1 + sumd d + Z.of_nat k)%Z /\
    (φ (PArray.length (bcur st))) = m /\ (φ (PArray.length (bact st))) = m /\
    (forall i, In i (firstn k (Ld d)) ->
       ((φ ((bcur st).[i])) < (φ (tn (bt st))))%Z /\ W ((bcur st).[i]) = firstn (S d) (pw i)) /\
    (forall i, ((φ i) < m)%Z -> ~ In i (firstn k (Ld d)) ->
       ((φ ((bcur st).[i])) < (φ (tn (bt st))))%Z /\ W ((bcur st).[i]) = firstn d (pw i)) /\
    (forall j : int, (Z.of_nat k <= (φ j) < Z.of_nat (List.length (Ld d)))%Z ->
       (bact st).[j] = nth (Z.to_nat (φ j)) (Ld d) 0) /\
    (φ (bw st)) = Z.of_nat (List.length (Lk d k)) /\
    (forall j : int, ((φ j) < (φ (bw st)))%Z -> (bact st).[j] = nth (Z.to_nat (φ j)) (Lk d k) 0).

  Lemma round_loop_spec : forall cap, cap = (1 + Ptot)%Z ->
    forall d dm, (φ dm) = Z.of_nat d -> forall na, (φ na) = Z.of_nat (List.length (Ld d)) ->
    forall z k km st H, gap na km = z -> (φ km) = Z.of_nat k ->
    (k <= List.length (Ld d))%nat -> RI cap d k st ->
    RI cap d (List.length (Ld d)) (round_loop pats dm na km st H).
  Proof.
    intros cap Hcap d dm Hdm na Hna z.
    induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros k km st H Hz Hkm Hk HI. rewrite round_loop_eq.
    destruct (bdec (km <? na)) as [Hlt | Hge].
    2:{ apply ltb_false in Hge. replace (List.length (Ld d)) with k by lia. exact HI. }
    pose proof (ltb_true _ _ Hlt) as Hlt'.
    destruct HI as (W & Ht & Hdp & HN & Hlc & Hla & Hc1 & Hc2 & Ha1 & Hw & Ha2).
    pose proof m_bound as Hm.
    pose proof (Ld_len d) as HLd.
    set (act := bact st). set (cur := bcur st). set (t := bt st). fold act cur t in Ht, Hdp, HN, Hlc, Hla, Hc1, Hc2, Ha1, Hw, Ha2.
    cbv zeta.
    assert (Ei : act.[km] = nth k (Ld d) 0)
      by (rewrite (Ha1 km ltac:(lia)); f_equal; lia).
    set (i := act.[km]) in *.
    assert (Hin : In i (Ld d)) by (rewrite Ei; apply nth_In; lia).
    pose proof Hin as Hin'. apply Ld_In in Hin' as [Him Hid].
    assert (Hnin : ~ In i (firstn k (Ld d)))
      by (rewrite Ei; apply nth_not_in_firstn; [apply Ld_NoDup | lia]).
    destruct (Hc2 i Him Hnin) as [Hu HWu].
    set (u := cur.[i]) in *.
    pose proof (plen_len i) as Hpl.
    assert (HlWu : List.length (W u) = d)
      by (rewrite HWu, length_firstn; lia).
    set (c := PrimString.get pats.[i] dm).
    assert (Hc : nth d (pw i) 0%Z = (φ c)).
    { unfold c. rewrite <- pstr_nth by (unfold plen in Hid; lia). unfold pw. f_equal. lia. }
    assert (HSd : firstn (S d) (pw i) = W u ++ [(φ c)])
      by (rewrite HWu, <- Hc; apply firstn_snoc; lia).
    pose proof (sumd_S d) as HS. pose proof (sumd_le (S d)) as HSle.
    destruct (add_child_spec t cap W u c Ht Hu ltac:(lia) ltac:(intros x Hx; rewrite HlWu; apply Hdp; exact Hx))
      as (W' & Ht' & HWo & HN' & Hv & HWv & Hnew).
    set (tv := add_child t u c) in *.
    set (v := snd tv) in *.
    set (t' := fst tv) in *.
    pose proof (ti_n _ _ _ Ht) as HN1.
    assert (Hlcur : (φ (PArray.length cur)) = m) by exact Hlc.
    assert (Hlact : (φ (PArray.length act)) = m) by exact Hla.
    assert (Hfk : firstn (S k) (Ld d) = firstn k (Ld d) ++ [i])
      by (rewrite Ei; apply firstn_snoc_gen; lia).
    assert (Hkm1 : (φ (km + 1)) = Z.of_nat (S k)) by (rewrite phi_add1; [lia | rewrite wB_val; lia]).
    assert (Hdec : Zwf 0 (gap na (km + 1)) z) by (rewrite <- Hz; apply dec_step; exact Hlt).
    assert (Hlenk : (S k <= List.length (Ld d))%nat) by lia.
    (* the common part of the new invariant: trie, depths, cur *)
    assert (Hcur : forall i', ((φ i') < m)%Z ->
      (In i' (firstn (S k) (Ld d)) ->
        ((φ (cur.[i <- v].[i'])) < (φ (tn t')))%Z /\ W' (cur.[i <- v].[i']) = firstn (S d) (pw i')) /\
      (~ In i' (firstn (S k) (Ld d)) ->
        ((φ (cur.[i <- v].[i'])) < (φ (tn t')))%Z /\ W' (cur.[i <- v].[i']) = firstn d (pw i'))).
    { intros i' Hi'. rewrite Hfk. destruct (int_eq_dec i' i) as [-> | Hne].
      - rewrite aget_set_same by lia. split.
        + intros _. split; [exact Hv | rewrite HWv, HSd; reflexivity].
        + intros F. exfalso. apply F. apply in_or_app. right. left. reflexivity.
      - rewrite aget_set_other by (intro F; apply Hne; symmetry; exact F).
        assert (Hno : In i' (firstn k (Ld d) ++ [i]) <-> In i' (firstn k (Ld d))).
        { rewrite in_app_iff. simpl. split; [intros [H1 | [H1 | []]]; [exact H1 | congruence] | intros H1; left; exact H1]. }
        rewrite Hno. split.
        + intros H1. destruct (Hc1 i' H1) as [H2 H3]. split; [lia | rewrite HWo by exact H2; exact H3].
        + intros H1. destruct (Hc2 i' Hi' H1) as [H2 H3]. split; [lia | rewrite HWo by exact H2; exact H3]. }
    assert (Hdp' : forall x, ((φ x) < (φ (tn t')))%Z -> (List.length (W' x) <= S d)%nat).
    { intros x Hx. destruct (Hnew x Hx) as [Hx' | Ex].
      - rewrite HWo by exact Hx'. apply Hdp. exact Hx'.
      - rewrite Ex, length_app, HlWu. simpl. lia. }
    assert (HN'' : ((φ (tn t')) <= 1 + sumd d + Z.of_nat (S k))%Z) by lia.
    assert (HLk : Lk d (S k) = Lk d k ++ (if (Z.of_nat (S d) <? plen i)%Z then [i] else [])).
    { unfold Lk. rewrite Hfk, filter_app. simpl. destruct (Z.of_nat (S d) <? plen i)%Z; reflexivity. }
    assert (Hwk : (List.length (Lk d k) <= k)%nat).
    { unfold Lk. pose proof (filter_length_le (fun i0 => Z.of_nat (S d) <? plen i0)%Z (firstn k (Ld d))).
      rewrite length_firstn in H0. lia. }
    assert (Hlcur' : (φ (PArray.length cur.[i <- v])) = m) by (rewrite alength_set; exact Hlcur).
    destruct (dm + 1 <? PrimString.length pats.[i]) eqn:Eb.
    - (* the pattern goes on *)
      apply ltb_true in Eb. rewrite phi_add1 in Eb by (unfold plen in Hid; rewrite Hdm; lia).
      assert (Eb' : (Z.of_nat (S d) <? plen i)%Z = true) by (apply Z.ltb_lt; unfold plen; lia).
      rewrite Eb' in HLk.
      eapply IH; [exact Hdec | reflexivity | exact Hkm1 | exact Hlenk |].
      exists W'. cbn [bt bcur bact bw]. split; [exact Ht'|]. split; [exact Hdp'|]. split; [exact HN''|].
      split; [exact Hlcur'|]. split; [rewrite alength_set; exact Hlact|].
      split; [intros i' Hi'; apply (Hcur i'); [exact (proj1 (proj1 (Ld_In d i') ltac:(eapply in_firstn'; exact Hi'))) | exact Hi']|].
      split; [intros i' Hi' Hn; apply (Hcur i' Hi'); exact Hn|].
      split.
      + intros j Hj. rewrite aget_set_other by (intro F; subst j; rewrite Hw in Hj; lia).
        apply Ha1. lia.
      + split.
        * rewrite HLk, length_app. simpl. rewrite phi_add1 by (rewrite Hw, wB_val; lia). lia.
        * intros j Hj. rewrite HLk.
          rewrite phi_add1 in Hj by (rewrite Hw, wB_val; lia).
          destruct (int_eq_dec j (bw st)) as [-> | Hjw].
          -- rewrite aget_set_same by lia. rewrite Hw. rewrite Nat2Z.id.
             rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
          -- rewrite aget_set_other by (intro F; apply Hjw; symmetry; exact F).
             pose proof (neq_phi _ _ Hjw).
             rewrite app_nth1 by lia. apply Ha2. lia.
    - (* the pattern ends here *)
      apply ltb_false in Eb. rewrite phi_add1 in Eb by (unfold plen in Hid; rewrite Hdm; lia).
      assert (Eb' : (Z.of_nat (S d) <? plen i)%Z = false) by (apply Z.ltb_ge; unfold plen; lia).
      rewrite Eb', app_nil_r in HLk.
      eapply IH; [exact Hdec | reflexivity | exact Hkm1 | exact Hlenk |].
      exists W'. cbn [bt bcur bact bw]. split; [exact Ht'|]. split; [exact Hdp'|]. split; [exact HN''|].
      split; [exact Hlcur'|]. split; [exact Hlact|].
      split; [intros i' Hi'; apply (Hcur i'); [exact (proj1 (proj1 (Ld_In d i') ltac:(eapply in_firstn'; exact Hi'))) | exact Hi']|].
      split; [intros i' Hi' Hn; apply (Hcur i' Hi'); exact Hn|].
      split; [intros j Hj; apply Ha1; lia|].
      rewrite HLk. split; [exact Hw | exact Ha2].
  Qed.

  Definition RS (cap : Z) (d : nat) (st : bstate) : Prop :=
    exists W, TrieInv (bt st) cap W /\
    (forall x, ((φ x) < (φ (tn (bt st))))%Z -> (List.length (W x) <= d)%nat) /\
    ((φ (tn (bt st))) <= 1 + sumd d)%Z /\
    (φ (PArray.length (bcur st))) = m /\ (φ (PArray.length (bact st))) = m /\
    (forall i, ((φ i) < m)%Z ->
       ((φ ((bcur st).[i])) < (φ (tn (bt st))))%Z /\ W ((bcur st).[i]) = firstn d (pw i)) /\
    (φ (bw st)) = Z.of_nat (List.length (Ld d)) /\
    (forall j : int, ((φ j) < (φ (bw st)))%Z -> (bact st).[j] = nth (Z.to_nat (φ j)) (Ld d) 0).

  Lemma filter_filter_imp : forall (f g : int -> bool) l,
    (forall x, f x = true -> g x = true) -> filter f (filter g l) = filter f l.
  Proof.
    intros f g l H. induction l as [| a l IH]; simpl; [reflexivity|].
    destruct (g a) eqn:Eg; simpl.
    - destruct (f a); rewrite IH; reflexivity.
    - destruct (f a) eqn:Ef; [rewrite (H a Ef) in Eg; discriminate | exact IH].
  Qed.

  Lemma Lk_full : forall d, Lk d (List.length (Ld d)) = Ld (S d).
  Proof.
    intros d. unfold Lk. rewrite firstn_all. unfold Ld at 1.
    apply filter_filter_imp. intros x Hx. apply Z.ltb_lt. apply Z.ltb_lt in Hx. lia.
  Qed.

  Lemma round_step : forall cap, cap = (1 + Ptot)%Z ->
    forall d dm, (φ dm) = Z.of_nat d -> forall st, RS cap d st ->
    RS cap (S d) (round_loop pats dm (bw st) 0 (mkB (bact st) (bcur st) 0 (bt st))
                    (Zwf_well_founded 0 (gap (bw st) 0))).
  Proof.
    intros cap Hcap d dm Hdm st HS.
    destruct HS as (W & Ht & Hdp & HN & Hlc & Hla & Hc & Hw & Ha).
    assert (HI : RI cap d 0 (mkB (bact st) (bcur st) 0 (bt st))).
    { exists W. cbn [bt bcur bact bw]. split; [exact Ht|].
      split; [intros x Hx; specialize (Hdp x Hx); lia|].
      split; [lia|]. split; [exact Hlc|]. split; [exact Hla|].
      split; [intros i []|].
      split; [intros i Hi _; exact (Hc i Hi)|].
      split; [intros j Hj; apply Ha; lia|].
      split; [reflexivity|]. intros j Hj. rewrite phi0 in Hj. pose proof (phi_bnd j). lia. }
    pose proof (round_loop_spec cap Hcap d dm Hdm (bw st) Hw _ 0%nat 0
                  (mkB (bact st) (bcur st) 0 (bt st)) (Zwf_well_founded 0 (gap (bw st) 0))
                  eq_refl phi0 ltac:(lia) HI) as HR.
    set (st' := round_loop _ _ _ _ _ _) in *.
    destruct HR as (W' & Ht' & Hdp' & HN' & Hlc' & Hla' & Hc1 & Hc2 & _ & Hw' & Ha2).
    exists W'. split; [exact Ht'|]. split; [exact Hdp'|].
    split; [rewrite sumd_S; lia|]. split; [exact Hlc'|]. split; [exact Hla'|].
    split.
    - intros i Hi. destruct (in_dec int_eq_dec i (Ld d)) as [Hin | Hnin].
      + apply Hc1. rewrite firstn_all. exact Hin.
      + rewrite firstn_all in Hc2. destruct (Hc2 i Hi Hnin) as [H1 H2].
        split; [exact H1|]. rewrite H2.
        assert (Hp : (plen i <= Z.of_nat d)%Z).
        { destruct (Z_le_gt_dec (plen i) (Z.of_nat d)) as [|Hg]; [assumption|].
          exfalso. apply Hnin. apply Ld_In. lia. }
        pose proof (plen_len i). rewrite !firstn_all2 by lia. reflexivity.
    - rewrite <- Lk_full. split; [exact Hw' | exact Ha2].
  Qed.

  Lemma rounds_spec : forall cap, cap = (1 + Ptot)%Z ->
    forall L, (forall i, ((φ i) < m)%Z -> (plen i <= (φ L))%Z) ->
    forall z d dm st H, gap L dm = z -> (φ dm) = Z.of_nat d -> (Z.of_nat d <= (φ L))%Z ->
    RS cap d st ->
    exists W, TrieInv (bt (rounds pats L dm st H)) cap W /\
      (φ (PArray.length (bcur (rounds pats L dm st H)))) = m /\
      forall i, ((φ i) < m)%Z ->
        ((φ ((bcur (rounds pats L dm st H)).[i])) < (φ (tn (bt (rounds pats L dm st H)))))%Z /\
        W ((bcur (rounds pats L dm st H)).[i]) = pw i.
  Proof.
    intros cap Hcap L HL z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros d dm st H Hz Hdm HdL HS. rewrite rounds_eq.
    destruct (bdec (dm <? L)) as [Hlt | Hge].
    - pose proof (ltb_true _ _ Hlt) as Hlt'. cbv zeta.
      eapply IH; [ | reflexivity | | | apply (round_step cap Hcap d dm Hdm st HS)].
      + rewrite <- Hz. apply dec_step. exact Hlt.
      + rewrite phi_add1 by (pose proof (phi_bnd L); lia). lia.
      + rewrite Nat2Z.inj_succ. lia.
    - apply ltb_false in Hge.
      destruct HS as (W & Ht & _ & _ & Hlc & _ & Hc & _).
      exists W. split; [exact Ht|]. split; [exact Hlc|].
      intros i Hi. destruct (Hc i Hi) as [H1 H2]. split; [exact H1|].
      rewrite H2. apply firstn_all2. pose proof (plen_len i). pose proof (HL i Hi). lia.
  Qed.

  Lemma iseq_S : forall k, (0 <= k)%Z -> iseq (k + 1) = iseq k ++ [of_Z k].
  Proof.
    intros k Hk. unfold iseq. replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
    rewrite seq_S, map_app. simpl. f_equal. f_equal. f_equal. lia.
  Qed.

  Lemma iseq_nth : forall k (j : int), ((φ j) < k)%Z -> (k < wB)%Z ->
    nth (Z.to_nat (φ j)) (iseq k) 0 = j.
  Proof.
    intros k j Hj Hk. unfold iseq. pose proof (phi_bnd j).
    set (g := fun k0 : nat => of_Z (Z.of_nat k0)).
    rewrite nth_indep with (d' := g 0%nat) by (rewrite length_map, length_seq; lia).
    rewrite map_nth, seq_nth by lia. unfold g. apply phi_inj. rewrite phi_of_Z; lia.
  Qed.

  Lemma zsum_iseq_mono : forall (f : int -> Z), (forall i, (0 <= f i)%Z) ->
    forall n r, (zsum f (iseq (Z.of_nat n)) <= zsum f (iseq (Z.of_nat (n + r))))%Z.
  Proof.
    intros f Hf n r. induction r as [| r IH]; [rewrite Nat.add_0_r; lia|].
    replace (Z.of_nat (n + S r)) with (Z.of_nat (n + r) + 1)%Z by lia.
    rewrite iseq_S, zsum_app by lia. simpl. pose proof (Hf (of_Z (Z.of_nat (n + r)))). lia.
  Qed.

  Lemma zsum_iseq_le : forall (f : int -> Z), (forall i, (0 <= f i)%Z) ->
    forall k, (0 <= k <= m)%Z -> (zsum f (iseq k) <= zsum f (iseq m))%Z.
  Proof.
    intros f Hf k Hk. pose proof m_bound.
    replace k with (Z.of_nat (Z.to_nat k)) by lia.
    replace m with (Z.of_nat (Z.to_nat k + (Z.to_nat m - Z.to_nat k))) by lia.
    apply zsum_iseq_mono. exact Hf.
  Qed.

  Lemma sums_eq : forall mm i P L H,
    sums pats mm i P L H =
    match bdec (i <? mm) with
    | left Hi =>
        let l := PrimString.length pats.[i] in
        sums pats mm (i + 1) (P + l) (if L <? l then l else L)
          (Acc_inv H (dec_step mm i Hi))
    | right _ => (P, L)
    end.
  Proof. intros. destruct H. reflexivity. Qed.

  Lemma sums_spec : (Ptot < 4194303)%Z ->
    forall z i P L H, gap (PArray.length pats) i = z -> ((φ i) <= m)%Z ->
    (φ P) = zsum plen (iseq (φ i)) ->
    (forall i', ((φ i') < (φ i))%Z -> (plen i' <= (φ L))%Z) ->
    (φ (fst (sums pats (PArray.length pats) i P L H))) = Ptot /\
    forall i', ((φ i') < m)%Z -> (plen i' <= (φ (snd (sums pats (PArray.length pats) i P L H))))%Z.
  Proof.
    intros HP z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros i P L H Hz Hi HPi HLi. rewrite sums_eq.
    pose proof m_bound as Hm.
    destruct (bdec (i <? PArray.length pats)) as [Hlt | Hge].
    - pose proof (ltb_true _ _ Hlt) as Hlt'. cbv zeta. fold m in Hlt'.
      pose proof (phi_bnd i).
      assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by (apply phi_add1; rewrite wB_val; lia).
      assert (HS : zsum plen (iseq ((φ i) + 1)) = (zsum plen (iseq (φ i)) + plen i)%Z).
      { rewrite iseq_S, zsum_app by lia. simpl. rewrite of_to_Z. lia. }
      assert (Hle : (zsum plen (iseq ((φ i) + 1)) <= Ptot)%Z)
        by (apply zsum_iseq_le; [intros j; apply plen_bnd | lia]).
      pose proof (zsum_nonneg plen (iseq (φ i)) (fun j _ => proj1 (plen_bnd j))).
      apply IH with (y := gap (PArray.length pats) (i + 1)); [rewrite <- Hz; apply dec_step; exact Hlt | reflexivity | lia | |].
      + rewrite Hi1, HS, add_spec, HPi.
        change (φ (PrimString.length pats.[i])) with (plen i).
        apply Z.mod_small. pose proof (plen_bnd i). rewrite HS in Hle. rewrite wB_val. lia.
      + intros i' Hi'. rewrite Hi1 in Hi'.
        destruct (L <? PrimString.length pats.[i]) eqn:EL.
        * apply ltb_true in EL. destruct (int_eq_dec i' i) as [-> | Hne]; [unfold plen; lia|].
          pose proof (neq_phi _ _ Hne). pose proof (HLi i' ltac:(lia)). lia.
        * apply ltb_false in EL. destruct (int_eq_dec i' i) as [-> | Hne]; [unfold plen; lia|].
          pose proof (neq_phi _ _ Hne). apply HLi. lia.
    - apply ltb_false in Hge. fold m in Hge. simpl.
      replace (φ i) with m in HPi by lia.
      split; [exact HPi|]. intros i' Hi'. apply HLi. lia.
  Qed.

  Lemma iota_eq : forall mm i a H,
    iota mm i a H =
    match bdec (i <? mm) with
    | left Hi => iota mm (i + 1) a.[i <- i] (Acc_inv H (dec_step mm i Hi))
    | right _ => a
    end.
  Proof. intros. destruct H. reflexivity. Qed.

  Lemma iota_spec : forall mm z i a H, gap mm i = z ->
    PArray.length a = mm -> ((φ i) <= (φ mm))%Z ->
    (forall j, ((φ j) < (φ i))%Z -> a.[j] = j) ->
    PArray.length (iota mm i a H) = mm /\
    forall j, ((φ j) < (φ mm))%Z -> (iota mm i a H).[j] = j.
  Proof.
    intros mm z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros i a H Hz Ha Hi Hj. rewrite iota_eq.
    destruct (bdec (i <? mm)) as [Hlt | Hge].
    - pose proof (ltb_true _ _ Hlt) as Hlt'. pose proof (ilen_bound a).
      assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by (apply phi_add1; rewrite wB_val; lia).
      apply IH with (y := gap mm (i + 1)); [rewrite <- Hz; apply dec_step; exact Hlt | reflexivity | rewrite alength_set; exact Ha | lia |].
      intros j Hj'. rewrite Hi1 in Hj'. destruct (int_eq_dec j i) as [-> | Hne].
      + apply aget_set_same. rewrite Ha. exact Hlt'.
      + rewrite aget_set_other by (intro F; apply Hne; symmetry; exact F).
        pose proof (neq_phi _ _ Hne). apply Hj. lia.
    - apply ltb_false in Hge. split; [exact Ha|]. intros j Hj'. apply Hj. lia.
  Qed.

  Lemma filter_all : forall (f : int -> bool) l, (forall x, In x l -> f x = true) -> filter f l = l.
  Proof.
    intros f l H. induction l as [| a l IH]; simpl; [reflexivity|].
    rewrite (H a (or_introl eq_refl)). rewrite IH; [reflexivity|]. intros x Hx. apply H. right. exact Hx.
  Qed.

  Lemma Ld0 : (forall i, ((φ i) < m)%Z -> (0 < plen i)%Z) -> Ld 0 = iseq m.
  Proof.
    intros Hp. unfold Ld. apply filter_all. intros x Hx.
    apply iseq_In in Hx; [|pose proof m_bound; rewrite wB_val; lia].
    apply Z.ltb_lt. apply Hp. exact Hx.
  Qed.

  (* The whole construction. *)
  Lemma build_spec :
    (forall i, ((φ i) < m)%Z -> (0 < plen i)%Z) -> (Ptot < 4194303)%Z ->
    let mm := PArray.length pats in
    let PL := sums pats mm 0 0 0 (Zwf_well_founded 0 (gap mm 0)) in
    let cap := fst PL + 1 in
    let L := snd PL in
    let t0 := mkT (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0)
                  (PArray.make cap 0) (PArray.make cap 0) 1 in
    let act0 := iota mm 0 (PArray.make mm 0) (Zwf_well_founded 0 (gap mm 0)) in
    let st := rounds pats L 0 (mkB act0 (PArray.make mm 0) mm t0)
                (Zwf_well_founded 0 (gap L 0)) in
    (φ cap) = (1 + Ptot)%Z /\
    exists W, TrieInv (bt st) (1 + Ptot) W /\
      (φ (PArray.length (bcur st))) = m /\
      forall i, ((φ i) < m)%Z ->
        ((φ ((bcur st).[i])) < (φ (tn (bt st))))%Z /\ W ((bcur st).[i]) = pw i.
  Proof.
    intros Hpos HP. cbv zeta.
    pose proof m_bound as Hm.
    pose proof (zsum_nonneg plen (iseq m) (fun j _ => proj1 (plen_bnd j))) as HP0.
    fold Ptot in HP0.
    destruct (sums_spec HP _ 0 0 0 (Zwf_well_founded 0 (gap (PArray.length pats) 0)) eq_refl
                ltac:(rewrite phi0; lia) ltac:(rewrite phi0; reflexivity)
                ltac:(intros i' Hi'; rewrite phi0 in Hi'; pose proof (phi_bnd i'); lia)) as [HPs HLs].
    set (PL := sums _ _ _ _ _ _) in *.
    assert (Hcap : (φ (fst PL + 1)) = (1 + Ptot)%Z) by (rewrite phi_add1; [lia | rewrite wB_val; lia]).
    split; [exact Hcap|].
    set (cap := fst PL + 1) in *.
    assert (Hmk : forall b : int, PArray.length (PArray.make cap b) = cap) by (intros b; apply amake_len; lia).
    assert (Hmm : PArray.length (PArray.make (PArray.length pats) 0) = PArray.length pats).
    { apply amake_len. exact (proj2 m_bound). }
    destruct (iota_spec (PArray.length pats) _ 0 (PArray.make (PArray.length pats) 0)
                (Zwf_well_founded 0 (gap (PArray.length pats) 0)) eq_refl Hmm
                ltac:(rewrite phi0; pose proof (phi_bnd (PArray.length pats)); lia)
                ltac:(intros j Hj; rewrite phi0 in Hj; pose proof (phi_bnd j); lia)) as [Hla Hia].
    set (act0 := iota _ _ _ _) in *.
    set (t0 := mkT _ _ _ _ _ 1).
    assert (HS0 : RS (1 + Ptot) 0 (mkB act0 (PArray.make (PArray.length pats) 0) (PArray.length pats) t0)).
    { exists (fun _ => []). cbn [bt bcur bact bw]. unfold t0. cbn [tn tchr tpar tfc tns tdep].
      split; [constructor; cbn [tn tchr tpar tfc tns tdep] |].
      - rewrite Hmk. exact Hcap.
      - rewrite Hmk. exact Hcap.
      - rewrite Hmk. exact Hcap.
      - rewrite Hmk. exact Hcap.
      - rewrite Hmk. exact Hcap.
      - rewrite phi1. lia.
      - reflexivity.
      - intros v Hv. rewrite phi1 in Hv. lia.
      - intros v Hv. rewrite aget_make. reflexivity.
      - intros u v Hu Hv _. rewrite phi1 in Hu, Hv. apply phi_inj.
        pose proof (phi_bnd u). pose proof (phi_bnd v). lia.
      - intros u v _ _ _. reflexivity.
      - intros v Hv. rewrite phi1 in Hv. lia.
      - intros u Hu v. rewrite aget_make. split; [intros F; exfalso; exact (Reach_0 _ _ F)|].
        rewrite phi1. lia.
      - intros u _. apply aget_make.
      - split; [intros x _; simpl; lia|].
        split; [rewrite phi1, sumd_0; lia|].
        split; [rewrite Hmm; reflexivity|].
        split; [unfold m; exact (f_equal to_Z Hla)|].
        split; [intros i Hi; rewrite aget_make, phi0, phi1; split; [lia | reflexivity]|].
        split; [rewrite (Ld0 Hpos), iseq_len, Z2Nat.id by lia; reflexivity|].
        intros j Hj. rewrite (Ld0 Hpos). unfold act0. rewrite Hia by exact Hj.
        symmetry. apply iseq_nth; [exact Hj | rewrite wB_val; lia]. }
    assert (HLb : forall i, ((φ i) < m)%Z -> (plen i <= (φ (snd PL)))%Z) by exact HLs.
    exact (rounds_spec (1 + Ptot) eq_refl (snd PL) HLb _ 0%nat 0 _ (Zwf_well_founded 0 (gap (snd PL) 0))
             eq_refl phi0 ltac:(pose proof (phi_bnd (snd PL)); lia) HS0).
  Qed.

  (* ---------------------------------------------------------------- *)
  (* The automaton, over the finished trie                             *)
  (* ---------------------------------------------------------------- *)

  Section Auto.
  Variable t : trie.
  Variable cap : Z.
  Variable W : int -> list Z.
  Variable cur : array int.
  Hypothesis Ht : TrieInv t cap W.
  Hypothesis Hlcur : (φ (PArray.length cur)) = m.
  Hypothesis Hcur : forall i, ((φ i) < m)%Z -> ((φ (cur.[i])) < (φ (tn t)))%Z /\ W (cur.[i]) = pw i.
  Hypothesis Hpos : forall i, ((φ i) < m)%Z -> (0 < plen i)%Z.
  Hypothesis Hm1 : (m < 4194303)%Z.

  Let N := tn t.

  Lemma plist_loop_eq : forall mm i fp np H,
    plist_loop cur mm i fp np H =
    match bdec (i <? mm) with
    | left Hi =>
        let v := cur.[i] in
        let old := fp.[v] in
        plist_loop cur mm (i + 1) fp.[v <- i + 1] np.[i + 1 <- old]
          (Acc_inv H (dec_step mm i Hi))
    | right _ => (fp, np)
    end.
  Proof. intros. destruct H. reflexivity. Qed.

  Definition PLI (i : Z) (fp np : array int) : Prop :=
    (φ (PArray.length fp)) = cap /\ (φ (PArray.length np)) = (m + 1)%Z /\
    (forall v, ((φ v) < (φ N))%Z -> forall e,
       Reach np (fp.[v]) e <-> ((1 <= (φ e) <= i)%Z /\ cur.[e - 1] = v)) /\
    (forall e, (1 <= (φ e) <= i)%Z -> ((φ (np.[e])) < (φ e))%Z) /\
    (forall v, ((φ v) < (φ N))%Z -> ((φ (fp.[v])) <= i)%Z).

  Lemma phi_sub1 : forall e : int, (1 <= (φ e))%Z -> (φ (e - 1)) = ((φ e) - 1)%Z.
  Proof. intros e He. sia. Qed.

  Lemma plist_loop_spec : forall z i fp np H, gap (PArray.length pats) i = z ->
    ((φ i) <= m)%Z -> PLI (φ i) fp np ->
    PLI m (fst (plist_loop cur (PArray.length pats) i fp np H))
          (snd (plist_loop cur (PArray.length pats) i fp np H)).
  Proof.
    intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros i fp np H Hz Hi HI. rewrite plist_loop_eq.
    pose proof m_bound as Hm.
    destruct (bdec (i <? PArray.length pats)) as [Hlt | Hge].
    2:{ apply ltb_false in Hge. fold m in Hge. simpl. replace m with (φ i) by lia. exact HI. }
    pose proof (ltb_true _ _ Hlt) as Hlt'. fold m in Hlt'. cbv zeta.
    destruct HI as (Hlf & Hln & P1 & P2 & P3).
    pose proof (phi_bnd i).
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by (apply phi_add1; rewrite wB_val; lia).
    destruct (Hcur i Hlt') as [Hv _].
    set (v := cur.[i]) in *.
    pose proof (ti_n _ _ _ Ht) as HN. fold N in HN.
    assert (He1 : (i + 1) - 1 = i) by (apply phi_inj; rewrite phi_sub1; lia).
    apply IH with (y := gap (PArray.length pats) (i + 1));
      [rewrite <- Hz; apply dec_step; exact Hlt | reflexivity | lia |].
    rewrite Hi1. split; [|split; [|split; [|split]]].
    - rewrite alength_set. exact Hlf.
    - rewrite alength_set. exact Hln.
    - intros v' Hv' e.
      assert (Hfr : forall a, ((φ a) <= (φ i))%Z ->
                (forall x, Reach np a x -> x <> i + 1)).
      { intros a Ha x Hr F. subst x.
        pose proof (Reach_le np (φ i) (fun x Hx => P2 x ltac:(lia)) a (i + 1) Ha Hr). lia. }
      destruct (int_eq_dec v' v) as [-> | Hne].
      + rewrite aget_set_same by lia.
        assert (He0 : i + 1 <> 0) by (apply nz_of_pos; lia).
        rewrite (Reach_cons _ _ e He0). rewrite aget_set_same by lia.
        rewrite (Reach_frame np (fp.[v]) (i + 1) (fp.[v]) e (Hfr _ (P3 v Hv))).
        rewrite (P1 v Hv e). split.
        * intros [-> | [H1 H2]]; [split; [lia | rewrite He1; reflexivity] | split; [lia | exact H2]].
        * intros [H1 H2]. destruct (Z.eq_dec (φ e) ((φ i) + 1)) as [E | E].
          -- left. apply phi_inj. rewrite Hi1. exact E.
          -- right. split; [lia | exact H2].
      + rewrite aget_set_other by (intro F; apply Hne; symmetry; exact F).
        rewrite (Reach_frame np (fp.[v']) (i + 1) (fp.[v]) e (Hfr _ (P3 v' Hv'))).
        rewrite (P1 v' Hv' e). split.
        * intros [H1 H2]. split; [lia | exact H2].
        * intros [H1 H2]. split; [|exact H2].
          destruct (Z.eq_dec (φ e) ((φ i) + 1)) as [E | E]; [|lia].
          exfalso. apply Hne.
          assert (Hei : e - 1 = i) by (apply phi_inj; rewrite phi_sub1 by lia; lia).
          rewrite <- H2, Hei. reflexivity.
    - intros e He. destruct (int_eq_dec e (i + 1)) as [-> | Hne].
      + rewrite aget_set_same by lia. pose proof (P3 v Hv). lia.
      + rewrite aget_set_other by (intro F; apply Hne; symmetry; exact F).
        apply P2. assert ((φ e) <> (φ i) + 1)%Z by (intro F; apply Hne; apply phi_inj; lia). lia.
    - intros v' Hv'. destruct (int_eq_dec v' v) as [-> | Hne].
      + rewrite aget_set_same by lia. lia.
      + rewrite aget_set_other by (intro F; apply Hne; symmetry; exact F).
        pose proof (P3 v' Hv'). lia.
  Qed.

  Section Links.
  Variables fp np : array int.
  Hypothesis Hlfp : (φ (PArray.length fp)) = cap.
  Hypothesis HP1 : forall v, ((φ v) < (φ N))%Z -> forall e,
    Reach np (fp.[v]) e <-> ((1 <= (φ e) <= m)%Z /\ cur.[e - 1] = v).
  Hypothesis HP2 : forall e, (1 <= (φ e) <= m)%Z -> ((φ (np.[e])) < (φ e))%Z.

  Definition Term (x : int) : Prop := exists i, ((φ i) < m)%Z /\ cur.[i] = x.

  Lemma term_fp : forall v, ((φ v) < (φ N))%Z -> (fp.[v] <> 0 <-> Term v).
  Proof.
    intros v Hv. split.
    - intros Hn. assert (Hr : Reach np (fp.[v]) (fp.[v])) by (constructor; exact Hn).
      apply (HP1 v Hv) in Hr as [H1 H2]. exists (fp.[v] - 1). split; [|exact H2].
      rewrite phi_sub1 by lia. lia.
    - intros [i [Hi Hc]] E. pose proof (phi_bnd i).
      assert (Hr : (1 <= (φ (i + 1)) <= m)%Z /\ cur.[(i + 1) - 1] = v).
      { assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by (apply phi_add1; rewrite wB_val; lia).
        split; [lia|]. replace ((i + 1) - 1) with i; [exact Hc|].
        apply phi_inj. rewrite phi_sub1; lia. }
      apply (HP1 v Hv) in Hr. rewrite E in Hr. exact (Reach_0 _ _ Hr).
  Qed.

  Lemma term_word : forall x, ((φ x) < (φ N))%Z -> Term x -> exists i, ((φ i) < m)%Z /\ W x = pw i.
  Proof.
    intros x Hx [i [Hi Hc]]. exists i. split; [exact Hi|].
    destruct (Hcur i Hi) as [_ E]. rewrite <- Hc. exact E.
  Qed.

  Lemma pw_term : forall i x, ((φ i) < m)%Z -> ((φ x) < (φ N))%Z -> W x = pw i -> Term x.
  Proof.
    intros i x Hi Hx E. exists i. split; [exact Hi|].
    destruct (Hcur i Hi) as [H1 H2]. apply (ti_inj _ _ _ Ht); [exact H1 | exact Hx | congruence].
  Qed.

  Lemma pw_node : forall i, ((φ i) < m)%Z -> IsNode t W (pw i).
  Proof. intros i Hi. destruct (Hcur i Hi) as [H1 H2]. exists (cur.[i]). split; assumption. Qed.

  Definition FailOK (fl : array int) (x : int) : Prop :=
    ((φ (fl.[x])) < (φ N))%Z /\ suffix (W (fl.[x])) (W x) /\
    (List.length (W (fl.[x])) < List.length (W x))%nat /\
    forall y, suffix y (W x) -> (List.length y < List.length (W x))%nat -> IsNode t W y ->
      (List.length y <= List.length (W (fl.[x])))%nat.

  Definition OutOK (out : array int) (x : int) : Prop :=
    ((φ (out.[x])) < (φ N))%Z /\
    (out.[x] <> 0 -> Term (out.[x]) /\ suffix (W (out.[x])) (W x) /\
                    (List.length (W (out.[x])) < List.length (W x))%nat) /\
    (forall i, ((φ i) < m)%Z -> suffix (pw i) (W x) ->
       (List.length (pw i) < List.length (W x))%nat ->
       (List.length (pw i) <= List.length (W (out.[x])))%nat).

  Lemma walk_eq : forall fl c x H,
    walk t fl c x H =
    let y := lookup t x c in
    match bdec (y =? 0) with
    | right _ => y
    | left _ =>
        match bdec (x =? 0) with
        | left _ => 0
        | right _ =>
            let x' := fl.[x] in
            match bdec (x' <? x) with
            | left Hx => walk t fl c x' (Acc_inv H (dec_lt x x' Hx))
            | right _ => 0
            end
        end
    end.
  Proof. intros. destruct H. reflexivity. Qed.

  Lemma walk_spec : forall fl X c (B : nat),
    (forall x, (0 < (φ x) < (φ N))%Z -> (List.length (W x) < B)%nat -> FailOK fl x) ->
    forall z x H, (φ x) = z -> ((φ x) < (φ N))%Z -> suffix (W x) X -> (List.length (W x) < B)%nat ->
    (forall y, suffix y X -> (List.length y < B)%nat -> IsNode t W (y ++ [(φ c)]) ->
       (List.length y <= List.length (W x))%nat) ->
    ((φ (walk t fl c x H)) < (φ N))%Z /\
    (W (walk t fl c x H) = [] \/
     exists y, W (walk t fl c x H) = y ++ [(φ c)] /\ suffix y X /\ (List.length y < B)%nat) /\
    (forall y, suffix y X -> (List.length y < B)%nat -> IsNode t W (y ++ [(φ c)]) ->
       (S (List.length y) <= List.length (W (walk t fl c x H)))%nat).
  Proof.
    intros fl X c B HF z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros x H Hz Hx HxX HxB Hmax. rewrite walk_eq. cbv zeta.
    destruct (lookup_spec t cap W x c Ht Hx) as [L1 L2].
    pose proof (ti_n _ _ _ Ht) as HN. fold N in HN.
    destruct (bdec (lookup t x c =? 0)) as [E | E].
    - apply eqb_true in E. specialize (L2 E).
      destruct (bdec (x =? 0)) as [E0 | E0].
      + apply eqb_true in E0. subst x. rewrite (ti_root _ _ _ Ht) in *.
        split; [rewrite phi0; lia|]. split; [left; reflexivity|].
        intros y Hy HyB Hn. exfalso. specialize (Hmax y Hy HyB Hn). simpl in Hmax.
        destruct y; [|simpl in Hmax; lia]. exact (L2 Hn).
      + apply eqb_false in E0. pose proof (pos_of_nz x E0) as Hx0.
        destruct (HF x ltac:(lia) HxB) as (Hf1 & Hf2 & Hf3 & Hf4).
        assert (Hfx : ((φ (fl.[x])) < (φ x))%Z) by (apply (ti_lt _ _ _ _ _ Ht); [exact Hf1 | exact Hx | exact Hf3]).
        destruct (bdec (fl.[x] <? x)) as [Hlt | Hge].
        2:{ exfalso. apply ltb_false in Hge. lia. }
        apply IH with (y := (φ (fl.[x]))); [rewrite <- Hz; apply dec_lt; exact Hlt | reflexivity | exact Hf1 | | lia |].
        * exact (suffix_trans _ _ _ Hf2 HxX).
        * intros y Hy HyB Hn. pose proof (Hmax y Hy HyB Hn) as Hle.
          pose proof (suffix_both y (W x) X Hy HxX Hle) as Hyx.
          destruct (Nat.eq_dec (List.length y) (List.length (W x))) as [Eq | Ne].
          -- exfalso. apply L2. rewrite <- (suffix_eq y (W x) X Hy HxX Eq). exact Hn.
          -- apply Hf4; [exact Hyx | lia | exact (isnode_prefix _ _ _ _ _ Ht Hn)].
    - apply eqb_false in E. destruct (L1 E) as [Hy Ew].
      split; [lia|]. split; [right; exists (W x); split; [exact Ew | split; assumption]|].
      intros y Hy2 HyB Hn. rewrite Ew, length_app. simpl. pose proof (Hmax y Hy2 HyB Hn). lia.
  Qed.

  Lemma fail_loop_eq : forall fp' NN v fl out H,
    fail_loop t fp' NN v fl out H =
    match bdec (v <? NN) with
    | left Hv =>
        let u := (tpar t).[v] in
        let c := (tchr t).[v] in
        let f := if u =? 0 then 0
                 else let x := fl.[u] in walk t fl c x (Zwf_well_founded 0 (φ x)) in
        let o := if fp'.[f] =? 0 then out.[f] else f in
        fail_loop t fp' NN (v + 1) fl.[v <- f] out.[v <- o]
          (Acc_inv H (dec_step NN v Hv))
    | right _ => (fl, out)
    end.
  Proof. intros. destruct H. reflexivity. Qed.

  Definition FI (v : Z) (fl out : array int) : Prop :=
    (φ (PArray.length fl)) = cap /\ (φ (PArray.length out)) = cap /\
    (forall x, (0 < (φ x) < v)%Z -> FailOK fl x) /\
    (forall x, ((φ x) < v)%Z -> OutOK out x).

  Lemma FailOK_set : forall fl x v f, x <> v -> FailOK fl x -> FailOK fl.[v <- f] x.
  Proof.
    intros fl x v f Hne H. unfold FailOK in *.
    rewrite aget_set_other by (intro F; apply Hne; symmetry; exact F). exact H.
  Qed.

  Lemma OutOK_set : forall out x v o, x <> v -> OutOK out x -> OutOK out.[v <- o] x.
  Proof.
    intros out x v o Hne H. unfold OutOK in *.
    rewrite aget_set_other by (intro F; apply Hne; symmetry; exact F). exact H.
  Qed.

  Lemma fail_loop_spec : forall z v fl out H, gap N v = z ->
    (1 <= (φ v) <= (φ N))%Z -> FI (φ v) fl out ->
    FI (φ N) (fst (fail_loop t fp N v fl out H)) (snd (fail_loop t fp N v fl out H)).
  Proof.
    intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros v fl out H Hz Hv HI. rewrite fail_loop_eq.
    pose proof (ti_n _ _ _ Ht) as HN. fold N in HN. pose proof (ti_cap _ _ _ Ht) as Hcap4.
    destruct (bdec (v <? N)) as [Hlt | Hge].
    2:{ apply ltb_false in Hge. simpl. replace (φ N) with (φ v) by lia. exact HI. }
    pose proof (ltb_true _ _ Hlt) as Hlt'. cbv zeta.
    destruct HI as (Hlfl & Hlout & HF & HO).
    assert (Hv1 : (φ (v + 1)) = ((φ v) + 1)%Z) by (apply phi_add1; rewrite wB_val; lia).
    destruct (ti_par _ _ _ Ht v ltac:(lia)) as [Hpu Ewv].
    set (u := (tpar t).[v]) in *. set (c := (tchr t).[v]) in *.
    pose proof (phi_bnd u) as Hu0.
    assert (HlWv : List.length (W v) = S (List.length (W u))) by (rewrite Ewv, length_app; simpl; lia).
    (* the failure link of v *)
    set (f := if u =? 0 then 0 else walk t fl c (fl.[u]) (Zwf_well_founded 0 (φ (fl.[u])))).
    assert (HFv : ((φ f) < (φ N))%Z /\ suffix (W f) (W v) /\ (List.length (W f) < List.length (W v))%nat /\
       forall y, suffix y (W v) -> (List.length y < List.length (W v))%nat -> IsNode t W y ->
         (List.length y <= List.length (W f))%nat).
    { unfold f. destruct (u =? 0) eqn:Eu.
      - apply eqb_true in Eu. rewrite Eu in Ewv, HlWv. rewrite (ti_root _ _ _ Ht) in *.
        split; [rewrite phi0; lia|]. split; [apply suffix_nil|]. split; [simpl; lia|].
        intros y _ Hy _. simpl in *. lia.
      - apply eqb_false in Eu. pose proof (pos_of_nz u Eu).
        destruct (HF u ltac:(lia)) as (Hf1 & Hf2 & Hf3 & Hf4).
        destruct (walk_spec fl (W u) c (List.length (W u))
                   ltac:(intros x Hx HxB; apply HF; split; [lia|];
                         apply (ti_lt _ _ _ _ _ Ht); [lia | lia | lia])
                   _ (fl.[u]) (Zwf_well_founded 0 (φ (fl.[u]))) eq_refl Hf1 Hf2 Hf3
                   ltac:(intros y Hy HyB Hn; apply Hf4; [exact Hy | exact HyB | exact (isnode_prefix _ _ _ _ _ Ht Hn)]))
          as (Hr1 & Hr2 & Hr3).
        set (r := walk _ _ _ _ _) in *.
        split; [exact Hr1|]. split; [|split].
        + destruct Hr2 as [E | (y & E & Hy & HyB)]; rewrite E; [apply suffix_nil|].
          rewrite Ewv. apply suffix_snoc. split; [reflexivity | exact Hy].
        + destruct Hr2 as [E | (y & E & Hy & HyB)]; rewrite E; simpl; [lia|].
          rewrite length_app. simpl. lia.
        + intros y' Hy' Hl Hn. rewrite Ewv in Hy'.
          destruct (suffix_snoc_cases y' (W u) (φ c) Hy') as [-> | (y & -> & Hy)]; [simpl; lia|].
          rewrite length_app in Hl |- *. simpl in Hl |- *.
          pose proof (Hr3 y Hy ltac:(lia) Hn). lia. }
    destruct HFv as (Hf1 & Hf2 & Hf3 & Hf4).
    assert (Hfv : ((φ f) < (φ v))%Z) by (apply (ti_lt _ _ _ _ _ Ht); [exact Hf1 | lia | exact Hf3]).
    destruct (HO f Hfv) as (Ho1 & Ho2 & Ho3).
    set (o := if fp.[f] =? 0 then out.[f] else f).
    assert (Hpw_f : forall i, ((φ i) < m)%Z -> suffix (pw i) (W v) ->
              (List.length (pw i) < List.length (W v))%nat -> (List.length (pw i) <= List.length (W f))%nat)
      by (intros i Hi Hs Hl; apply Hf4; [exact Hs | exact Hl | apply pw_node; exact Hi]).
    assert (HOv : OutOK out.[v <- o] v).
    { unfold OutOK. rewrite aget_set_same by lia. unfold o.
      destruct (fp.[f] =? 0) eqn:Ef.
      - apply eqb_true in Ef.
        assert (Hnt : ~ Term f) by (intro T; apply (proj2 (term_fp f Hf1)) in T; exact (T Ef)).
        split; [exact Ho1|]. split.
        + intros Hn. destruct (Ho2 Hn) as (T & S1 & S2).
          split; [exact T|]. split; [exact (suffix_trans _ _ _ S1 Hf2) | lia].
        + intros i Hi Hs Hl. pose proof (Hpw_f i Hi Hs Hl) as Hle.
          pose proof (suffix_both _ _ _ Hs Hf2 Hle) as Hsf.
          destruct (Nat.eq_dec (List.length (pw i)) (List.length (W f))) as [Eq | Ne].
          * exfalso. apply Hnt. apply (pw_term i f Hi Hf1).
            symmetry. exact (suffix_eq _ _ _ Hs Hf2 Eq).
          * apply Ho3; [exact Hi | exact Hsf | lia].
      - apply eqb_false in Ef.
        split; [exact Hf1|]. split.
        + intros _. split; [apply (term_fp f Hf1); exact Ef | split; [exact Hf2 | exact Hf3]].
        + exact Hpw_f. }
    apply IH with (y := gap N (v + 1)); [rewrite <- Hz; apply dec_step; exact Hlt | reflexivity | lia |].
    rewrite Hv1. split; [rewrite alength_set; exact Hlfl|]. split; [rewrite alength_set; exact Hlout|].
    split.
    - intros x Hx. destruct (int_eq_dec x v) as [-> | Hne].
      + unfold FailOK. rewrite aget_set_same by lia. split; [exact Hf1|]. split; [exact Hf2|].
        split; [exact Hf3 | exact Hf4].
      + apply FailOK_set; [exact Hne|]. apply HF. pose proof (neq_phi _ _ Hne). lia.
    - intros x Hx. destruct (int_eq_dec x v) as [-> | Hne]; [exact HOv|].
      apply OutOK_set; [exact Hne|]. apply HO. pose proof (neq_phi _ _ Hne). lia.
  Qed.

  (* -------------------------------------------------------------- *)
  (* The text pass                                                   *)
  (* -------------------------------------------------------------- *)

  Definition suffixb (y X : list Z) : bool :=
    if list_eq_dec Z.eq_dec (skipn (List.length X - List.length y) X) y
    then (List.length y <=? List.length X)%nat else false.

  Lemma suffixb_spec : forall y X, suffixb y X = true <-> suffix y X.
  Proof.
    intros y X. rewrite suffix_skipn. unfold suffixb.
    destruct (list_eq_dec Z.eq_dec _ _) as [E | E].
    - rewrite Nat.leb_le. tauto.
    - split; [discriminate | tauto].
  Qed.

  Lemma Reach_trans : forall ns a b c, Reach ns a b -> Reach ns b c -> Reach ns a c.
  Proof.
    intros ns a b c H1. induction H1 as [a Ha | a b Ha H IH]; intros H2; [exact H2|].
    apply R_next; [exact Ha | apply IH; exact H2].
  Qed.

  Section ScanProof.
  Variables fl out : array int.
  Hypothesis HFI : FI (φ N) fl out.
  Variable txt : PrimString.string.

  Definition T : list Z := pstr txt.
  Definition occb (i : int) (j : nat) : bool := suffixb (pw i) (firstn (S j) T).
  Definition pos (j : nat) (i : int) : Z := (Z.of_nat j + 1 - plen i)%Z.
  Definition Acc_ (j : nat) (i : int) : list Z :=
    map (fun j' => pos j' i) (filter (occb i) (seq 0 j)).
  Definition Full (i : int) : list Z := Acc_ (List.length T) i.

  Lemma Acc_S : forall j i, Acc_ (S j) i = Acc_ j i ++ (if occb i j then [pos j i] else []).
  Proof.
    intros j i. unfold Acc_. rewrite seq_S, filter_app, map_app. simpl.
    destruct (occb i j); reflexivity.
  Qed.

  Lemma Acc_prefix : forall j i, (j <= List.length T)%nat -> exists rest, Acc_ j i ++ rest = Full i.
  Proof.
    intros j i Hj. unfold Full, Acc_.
    replace (List.length T) with (j + (List.length T - j))%nat by lia.
    rewrite seq_app, filter_app, map_app. eexists. reflexivity.
  Qed.

  Definition Longest (X : list Z) (st : int) : Prop :=
    ((φ st) < (φ N))%Z /\ suffix (W st) X /\
    forall z, ((φ z) < (φ N))%Z -> suffix (W z) X -> (List.length (W z) <= List.length (W st))%nat.

  Variable Sx : Type.
  Variable R : Sx -> (int -> list Z) -> Prop.
  Variable f : Sx -> int -> int -> Sx.
  Hypothesis R_ext : forall s A B, (forall i, ((φ i) < m)%Z -> A i = B i) -> R s A -> R s B.
  Hypothesis Hf : forall s A i p, R s A -> ((φ i) < m)%Z ->
    (exists rest, A i ++ [(φ p)] ++ rest = Full i) ->
    R (f s i p) (fun i' => if i' =? i then A i ++ [(φ p)] else A i').

  (* during the step at text position j: the patterns of E have been
     recorded at j, the others not yet *)
  Definition EmInv (j : nat) (E : int -> Prop) (s : Sx) : Prop :=
    exists A, R s A /\ forall i, ((φ i) < m)%Z ->
      (E i /\ A i = Acc_ j i ++ [pos j i]) \/ (~ E i /\ A i = Acc_ j i).

  Lemma EmInv_iff : forall j E E' s, (forall i, ((φ i) < m)%Z -> (E i <-> E' i)) ->
    EmInv j E s -> EmInv j E' s.
  Proof.
    intros j E E' s HE [A [HR HA]]. exists A. split; [exact HR|].
    intros i Hi. rewrite <- (HE i Hi). exact (HA i Hi).
  Qed.

  Lemma emit_list_eq : forall p e s H,
    emit_list Sx f np p e s H =
    match bdec (e =? 0) with
    | left _ => s
    | right _ =>
        let s' := f s (e - 1) p in
        let e' := np.[e] in
        match bdec (e' <? e) with
        | left He => emit_list Sx f np p e' s' (Acc_inv H (dec_lt e e' He))
        | right _ => s'
        end
    end.
  Proof. intros. destruct H. reflexivity. Qed.

  Lemma emit_list_spec : forall j x p (E0 : int -> Prop),
    (j < List.length T)%nat -> ((φ x) < (φ N))%Z ->
    (φ p) = (Z.of_nat j + 1 - Z.of_nat (List.length (W x)))%Z ->
    (forall i, ((φ i) < m)%Z -> E0 i -> cur.[i] <> x) ->
    (forall i, ((φ i) < m)%Z -> cur.[i] = x -> occb i j = true) ->
    forall z e s H, (φ e) = z -> (e = 0 \/ Reach np (fp.[x]) e) ->
    EmInv j (fun i => E0 i \/ (cur.[i] = x /\ ~ Reach np e (i + 1))) s ->
    EmInv j (fun i => E0 i \/ cur.[i] = x) (emit_list Sx f np p e s H).
  Proof.
    intros j x p E0 Hj Hx Hp Hdis Hocc z.
    induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros e s H Hz He HI. rewrite emit_list_eq.
    pose proof m_bound as Hm.
    destruct (bdec (e =? 0)) as [E | E].
    - apply eqb_true in E. subst e. refine (EmInv_iff j _ _ s _ HI).
      intros i Hi. split; [intros [H1 | [H1 _]]; [left | right]; assumption|].
      intros [H1 | H1]; [left; exact H1 | right; split; [exact H1 | apply Reach_0]].
    - apply eqb_false in E. cbv zeta.
      destruct He as [He | He]; [contradiction|].
      pose proof He as He'. apply (HP1 x Hx e) in He' as [He1 He2].
      set (i0 := e - 1) in *.
      assert (Hi0 : (φ i0) = ((φ e) - 1)%Z) by (apply phi_sub1; lia).
      assert (Hi0m : ((φ i0) < m)%Z) by lia.
      assert (He0 : i0 + 1 = e) by (apply phi_inj; rewrite phi_add1; [lia | rewrite wB_val; lia]).
      destruct HI as [A [HR HA]].
      assert (HAi0 : A i0 = Acc_ j i0).
      { destruct (HA i0 Hi0m) as [[[F | [_ F]] _] | [_ E2]]; [| | exact E2].
        - exfalso. exact (Hdis i0 Hi0m F He2).
        - exfalso. apply F. rewrite He0. constructor. exact E. }
      assert (Hpos0 : pos j i0 = (φ p)).
      { unfold pos. rewrite Hp. destruct (Hcur i0 Hi0m) as [_ Ew]. rewrite He2 in Ew.
        rewrite Ew, plen_len. reflexivity. }
      assert (Hpre : exists rest, A i0 ++ [(φ p)] ++ rest = Full i0).
      { destruct (Acc_prefix (S j) i0 ltac:(lia)) as [rest Hrest].
        exists rest. rewrite HAi0, <- Hrest, Acc_S, (Hocc i0 Hi0m He2), Hpos0, <- app_assoc. reflexivity. }
      pose proof (Hf s A i0 p HR Hi0m Hpre) as HR'.
      pose proof (HP2 e ltac:(lia)) as Hne.
      destruct (bdec (np.[e] <? e)) as [Hlt | Hge].
      2:{ exfalso. apply ltb_false in Hge. lia. }
      apply IH with (y := (φ (np.[e]))); [rewrite <- Hz; apply dec_lt; exact Hlt | reflexivity | |].
      + destruct (int_eq_dec (np.[e]) 0) as [E0' | E0']; [left; exact E0'|].
        right. apply (Reach_trans _ _ e); [exact He | apply R_next; [exact E | constructor; exact E0']].
      + exists (fun i' => if i' =? i0 then A i0 ++ [(φ p)] else A i'). split; [exact HR'|].
        intros i Hi. destruct (int_eq_dec i i0) as [-> | Hii].
        * rewrite eqb_refl. left. split; [right; split; [exact He2|] | rewrite HAi0, Hpos0; reflexivity].
          intro Hr. rewrite He0 in Hr.
          pose proof (Reach_le np m (fun x0 Hx0 => HP2 x0 ltac:(lia)) (np.[e]) e ltac:(lia) Hr). lia.
        * replace (i =? i0) with false by (symmetry; apply eqb_false_spec; exact Hii).
          assert (Hie : i + 1 <> e).
          { intro F. apply Hii. apply phi_inj. rewrite Hi0. rewrite <- F.
            rewrite phi_add1; [lia | rewrite wB_val; lia]. }
          assert (Hiff : Reach np e (i + 1) <-> Reach np (np.[e]) (i + 1)).
          { rewrite (Reach_cons np e (i + 1) E). split; [intros [F | F]; [contradiction | exact F] | intros F; right; exact F]. }
          destruct (HA i Hi) as [[H1 H2] | [H1 H2]]; [left | right]; (split; [|exact H2]).
          -- destruct H1 as [H1 | [H1 H3]]; [left; exact H1 | right; split; [exact H1 | rewrite <- Hiff; exact H3]].
          -- intros [H3 | [H3 H4]]; apply H1; [left; exact H3 | right; split; [exact H3 | rewrite Hiff; exact H4]].
  Qed.

  Lemma emit_chain_eq : forall je x s H,
    emit_chain Sx f t out fp np je x s H =
    match bdec (x =? 0) with
    | left _ => s
    | right _ =>
        let e := fp.[x] in
        let s' := emit_list Sx f np (je - (tdep t).[x]) e s (Zwf_well_founded 0 (φ e)) in
        let o := out.[x] in
        match bdec (o <? x) with
        | left Ho => emit_chain Sx f t out fp np je o s' (Acc_inv H (dec_lt x o Ho))
        | right _ => s'
        end
    end.
  Proof. intros. destruct H. reflexivity. Qed.

  Definition Em (q x i : int) : Prop :=
    suffix (pw i) (W q) /\ (List.length (W x) < List.length (pw i))%nat.

  Lemma emit_chain_spec : forall j q je, (j < List.length T)%nat ->
    Longest (firstn (S j) T) q -> (φ je) = (Z.of_nat j + 1)%Z ->
    forall z x s H, (φ x) = z -> ((φ x) < (φ N))%Z -> suffix (W x) (W q) ->
    EmInv j (Em q x) s ->
    EmInv j (fun i => suffix (pw i) (W q)) (emit_chain Sx f t out fp np je x s H).
  Proof.
    intros j q je Hj [Hq1 [Hq2 Hq3]] Hje z.
    induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros x s H Hz Hx Hxq HI. rewrite emit_chain_eq.
    destruct HFI as (_ & _ & _ & HO).
    pose proof m_bound as Hm.
    destruct (bdec (x =? 0)) as [E | E].
    - apply eqb_true in E. subst x. refine (EmInv_iff j _ _ s _ HI).
      intros i Hi. unfold Em. rewrite (ti_root _ _ _ Ht). simpl.
      pose proof (Hpos i Hi). pose proof (plen_len i). split; [tauto|]. intros H3. split; [exact H3 | lia].
    - apply eqb_false in E. cbv zeta. pose proof (pos_of_nz x E) as Hx0.
      assert (HlX : List.length (firstn (S j) T) = S j) by (rewrite length_firstn; lia).
      pose proof (suffix_length _ _ Hxq) as Hl1. pose proof (suffix_length _ _ Hq2) as Hl2.
      assert (Hp : (φ (je - (tdep t).[x])) = (Z.of_nat j + 1 - Z.of_nat (List.length (W x)))%Z).
      { rewrite sub_spec, (ti_dep _ _ _ Ht x Hx), Hje. apply Z.mod_small. rewrite wB_val.
        lia. }
      assert (Hdis : forall i, ((φ i) < m)%Z -> Em q x i -> cur.[i] <> x).
      { intros i Hi [_ Hlt] Hc. destruct (Hcur i Hi) as [_ Ew]. rewrite Hc in Ew. rewrite Ew in Hlt. lia. }
      assert (Hocc : forall i, ((φ i) < m)%Z -> cur.[i] = x -> occb i j = true).
      { intros i Hi Hc. unfold occb. apply suffixb_spec. destruct (Hcur i Hi) as [_ Ew].
        rewrite Hc in Ew. rewrite <- Ew. exact (suffix_trans _ _ _ Hxq Hq2). }
      assert (HI' : EmInv j (fun i => Em q x i \/ (cur.[i] = x /\ ~ Reach np (fp.[x]) (i + 1))) s).
      { refine (EmInv_iff j _ _ s _ HI). intros i Hi. split; [intros H1; left; exact H1|].
        intros [H1 | [H1 H2]]; [exact H1|]. exfalso. apply H2. apply (HP1 x Hx).
        pose proof (phi_bnd i).
        assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by (apply phi_add1; rewrite wB_val; lia).
        split; [lia|]. replace ((i + 1) - 1) with i; [exact H1|].
        apply phi_inj. rewrite phi_sub1; lia. }
      pose proof (emit_list_spec j x _ (Em q x) Hj Hx Hp Hdis Hocc _ (fp.[x])
                    s (Zwf_well_founded 0 (φ (fp.[x]))) eq_refl
                    ltac:(destruct (int_eq_dec (fp.[x]) 0) as [E0 | E0]; [left; exact E0 | right; constructor; exact E0])
                    HI') as HL.
      set (s' := emit_list _ _ _ _ _ _ _) in *.
      destruct (HO x Hx) as (Ho1 & Ho2 & Ho3).
      assert (Hox : ((φ (out.[x])) < (φ x))%Z).
      { destruct (int_eq_dec (out.[x]) 0) as [E0 | E0]; [rewrite E0, phi0; lia|].
        destruct (Ho2 E0) as (_ & _ & Hlt). apply (ti_lt _ _ _ _ _ Ht); [exact Ho1 | exact Hx | exact Hlt]. }
      destruct (bdec (out.[x] <? x)) as [Hlt | Hge].
      2:{ exfalso. apply ltb_false in Hge. lia. }
      apply IH with (y := (φ (out.[x]))); [rewrite <- Hz; apply dec_lt; exact Hlt | reflexivity | exact Ho1 | |].
      + destruct (int_eq_dec (out.[x]) 0) as [E0 | E0]; [rewrite E0, (ti_root _ _ _ Ht); apply suffix_nil|].
        destruct (Ho2 E0) as (_ & S1 & _). exact (suffix_trans _ _ _ S1 Hxq).
      + refine (EmInv_iff j _ _ s' _ HL). intros i Hi. unfold Em.
        assert (HWo : (List.length (W (out.[x])) < List.length (W x))%nat).
        { destruct (int_eq_dec (out.[x]) 0) as [E0 | E0]; [|exact (proj2 (proj2 (Ho2 E0)))].
          rewrite E0, (ti_root _ _ _ Ht). simpl.
          destruct (List.length (W x)) eqn:El; [|lia]. exfalso.
          apply E. apply (ti_nil _ _ _ x Ht Hx). destruct (W x); [reflexivity | discriminate]. }
        destruct (Hcur i Hi) as [Hci Ewi].
        split.
        * intros [[H1 H2] | H1]; [split; [exact H1 | lia]|].
          rewrite H1 in Ewi. rewrite <- Ewi. split; [exact Hxq | exact HWo].
        * intros [H1 H2].
          destruct (Nat.lt_ge_cases (List.length (W x)) (List.length (pw i))) as [Hlt' | Hge'];
            [left; split; assumption|].
          right. pose proof (suffix_both _ _ _ H1 Hxq Hge') as Hsx.
          destruct (Nat.eq_dec (List.length (pw i)) (List.length (W x))) as [Eq | Ne].
          -- apply (ti_inj _ _ _ Ht); [exact Hci | exact Hx |].
             rewrite Ewi. exact (suffix_eq _ _ _ H1 Hxq Eq).
          -- exfalso. pose proof (Ho3 i Hi Hsx ltac:(lia)). lia.
  Qed.

  Lemma scan_eq : forall n j st s H,
    scan Sx f t fl out fp np txt n j st s H =
    match bdec (j <? n) with
    | left Hj =>
        let st' := walk t fl (PrimString.get txt j) st (Zwf_well_founded 0 (φ st)) in
        let s' := emit_chain Sx f t out fp np (j + 1) st' s (Zwf_well_founded 0 (φ st')) in
        scan Sx f t fl out fp np txt n (j + 1) st' s' (Acc_inv H (dec_step n j Hj))
    | right _ => s
    end.
  Proof. intros. destruct H. reflexivity. Qed.

  Lemma scan_spec : forall n, (φ n) = Z.of_nat (List.length T) ->
    forall z jm j st s H, gap n jm = z -> (φ jm) = Z.of_nat j -> (j <= List.length T)%nat ->
    Longest (firstn j T) st -> R s (Acc_ j) ->
    R (scan Sx f t fl out fp np txt n jm st s H) Full.
  Proof.
    intros n Hn z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros jm j st s H Hz Hjm Hj HL HR. rewrite scan_eq.
    pose proof HFI as (_ & _ & HF & _).
    destruct (bdec (jm <? n)) as [Hlt | Hge].
    2:{ apply ltb_false in Hge. replace j with (List.length T) in HR by lia. exact HR. }
    pose proof (ltb_true _ _ Hlt) as Hlt'. cbv zeta.
    assert (Hj' : (j < List.length T)%nat) by lia.
    assert (Hjm1 : (φ (jm + 1)) = (Z.of_nat j + 1)%Z) by (rewrite phi_add1; [lia | rewrite wB_val; pose proof (phi_bnd n); lia]).
    set (c := PrimString.get txt jm).
    assert (Hc : nth j T 0%Z = (φ c)).
    { unfold c, T. rewrite <- pstr_nth by (rewrite <- pstr_len; fold T; lia). f_equal. lia. }
    assert (HX : firstn (S j) T = firstn j T ++ [(φ c)]) by (rewrite <- Hc; apply firstn_snoc; exact Hj').
    destruct HL as (Hs1 & Hs2 & Hs3).
    destruct (walk_spec fl (firstn j T) c (S (List.length (firstn j T)))
                (fun x Hx _ => HF x Hx) _ st (Zwf_well_founded 0 (φ st)) eq_refl Hs1 Hs2
                ltac:(pose proof (suffix_length _ _ Hs2); lia)
                ltac:(intros y Hy _ Hn'; destruct (isnode_prefix _ _ _ _ _ Ht Hn') as [zz [Hzz Ew]];
                      rewrite <- Ew; apply Hs3; [exact Hzz | rewrite Ew; exact Hy]))
      as (Hr1 & Hr2 & Hr3).
    set (q := walk _ _ _ _ _) in *.
    assert (HLq : Longest (firstn (S j) T) q).
    { rewrite HX. split; [exact Hr1|]. split.
      - destruct Hr2 as [E | (y & E & Hy & _)]; rewrite E; [apply suffix_nil|].
        apply suffix_snoc. split; [reflexivity | exact Hy].
      - intros zz Hzz Hs. destruct (suffix_snoc_cases _ _ _ Hs) as [E | (y & E & Hy)];
          [rewrite E; simpl; lia|].
        rewrite E, length_app. simpl. rewrite Nat.add_1_r.
        apply Hr3; [exact Hy | pose proof (suffix_length _ _ Hy); lia | exists zz; split; [exact Hzz | exact E]]. }
    pose proof HLq as (Hq1 & Hq2 & Hq3).
    assert (HI : EmInv j (Em q q) s).
    { exists (Acc_ j). split; [exact HR|]. intros i Hi. right. split; [|reflexivity].
      intros [H1 H2]. pose proof (suffix_length _ _ H1). lia. }
    pose proof (emit_chain_spec j q (jm + 1) Hj' HLq Hjm1 _ q s (Zwf_well_founded 0 (φ q))
                  eq_refl Hq1 (suffix_refl _) HI) as HE.
    set (s' := emit_chain _ _ _ _ _ _ _ _ _ _) in *.
    destruct HE as [A [HRA HA]].
    apply IH with (y := gap n (jm + 1)) (j := S j);
      [rewrite <- Hz; apply dec_step; exact Hlt | reflexivity | rewrite Hjm1; lia | lia | exact HLq |].
    apply (R_ext s' A); [|exact HRA].
    intros i Hi. rewrite Acc_S.
    assert (Hoc : occb i j = true <-> suffix (pw i) (W q)).
    { unfold occb. rewrite suffixb_spec. split; [|intros H1; exact (suffix_trans _ _ _ H1 Hq2)].
      intros H1. destruct (Hcur i Hi) as [Hci Ewi].
      apply (suffix_both _ _ _ H1 Hq2). rewrite <- Ewi. apply Hq3; [exact Hci | rewrite Ewi; exact H1]. }
    destruct (HA i Hi) as [[H1 H2] | [H1 H2]].
    - rewrite (proj2 Hoc H1). exact H2.
    - destruct (occb i j) eqn:Eo; [exfalso; apply H1; apply Hoc; reflexivity|].
      rewrite app_nil_r. exact H2.
  Qed.

  End ScanProof.

  End Links.
  End Auto.

  (* ---------------------------------------------------------------- *)
  (* The two instances of the text pass: counting, filling            *)
  (* ---------------------------------------------------------------- *)

  Section Rows.
  Variable txt : PrimString.string.
  Hypothesis HT : (Z.of_nat (List.length (T txt)) <= 4194303)%Z.

  Lemma Full_len : forall i, (List.length (Full txt i) <= List.length (T txt))%nat.
  Proof.
    intros i. unfold Full, Acc_. rewrite length_map.
    etransitivity; [apply filter_length_le|]. rewrite length_seq. lia.
  Qed.

  Lemma prefix_len : forall (a b c : list Z), a ++ b = c -> (List.length a <= List.length c)%nat.
  Proof. intros a b c <-. rewrite length_app. lia. Qed.

  Definition Rcnt (cnt : array int) (A : int -> list Z) : Prop :=
    (φ (PArray.length cnt)) = m /\
    forall i, ((φ i) < m)%Z -> (φ (cnt.[i])) = Z.of_nat (List.length (A i)).

  Lemma Rcnt_ext : forall s A B, (forall i, ((φ i) < m)%Z -> A i = B i) -> Rcnt s A -> Rcnt s B.
  Proof.
    intros s A B HAB [H1 H2]. split; [exact H1|]. intros i Hi. rewrite <- HAB by exact Hi. apply H2. exact Hi.
  Qed.

  Lemma Rcnt_f : forall s A i p, Rcnt s A -> ((φ i) < m)%Z ->
    (exists rest, A i ++ [(φ p)] ++ rest = Full txt i) ->
    Rcnt (f_cnt s i p) (fun i' => if i' =? i then A i ++ [(φ p)] else A i').
  Proof.
    intros s A i p [H1 H2] Hi [rest Hr]. unfold f_cnt.
    pose proof (Full_len i) as HF. pose proof (prefix_len (A i ++ [(φ p)]) rest _ ltac:(rewrite <- app_assoc; exact Hr)) as Hl.
    rewrite length_app in Hl. simpl in Hl.
    split; [rewrite alength_set; exact H1|].
    intros i' Hi'. destruct (int_eq_dec i' i) as [-> | Hne].
    - rewrite eqb_refl, aget_set_same by lia. rewrite length_app. simpl.
      rewrite phi_add1; [rewrite H2 by exact Hi; lia | rewrite H2 by exact Hi; rewrite wB_val; lia].
    - replace (i' =? i) with false by (symmetry; apply eqb_false_spec; exact Hne).
      rewrite aget_set_other by (intro F; apply Hne; symmetry; exact F). apply H2. exact Hi'.
  Qed.

  Definition Rfill (st : array (array int) * array int) (A : int -> list Z) : Prop :=
    (φ (PArray.length (fst st))) = m /\ (φ (PArray.length (snd st))) = m /\
    forall i, ((φ i) < m)%Z ->
      (φ ((snd st).[i])) = Z.of_nat (List.length (A i)) /\
      (φ (PArray.length ((fst st).[i]))) = Z.of_nat (List.length (Full txt i)) /\
      forall k, ((φ k) < Z.of_nat (List.length (A i)))%Z ->
        (φ ((fst st).[i].[k])) = nth (Z.to_nat (φ k)) (A i) 0%Z.

  Lemma Rfill_ext : forall s A B, (forall i, ((φ i) < m)%Z -> A i = B i) -> Rfill s A -> Rfill s B.
  Proof.
    intros s A B HAB (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
    intros i Hi. rewrite <- HAB by exact Hi. apply H3. exact Hi.
  Qed.

  Lemma aalength_set : forall (t : array (array int)) (i : int) (b : array int),
    PArray.length t.[i <- b] = PArray.length t.
  Proof. intros t i b. exact (length_set (array int) t i b). Qed.

  Lemma aaget_set_same : forall (t : array (array int)) (i : int) (b : array int),
    ((φ i) < (φ (PArray.length t)))%Z -> t.[i <- b].[i] = b.
  Proof. intros t i b H. apply (get_set_same (array int) t i b). apply ltb_spec. exact H. Qed.

  Lemma aaget_set_other : forall (t : array (array int)) (i j : int) (b : array int),
    i <> j -> t.[i <- b].[j] = t.[j].
  Proof. intros t i j b H. exact (get_set_other (array int) t i j b H). Qed.

  Lemma Rfill_f : forall s A i p, Rfill s A -> ((φ i) < m)%Z ->
    (exists rest, A i ++ [(φ p)] ++ rest = Full txt i) ->
    Rfill (f_fill s i p) (fun i' => if i' =? i then A i ++ [(φ p)] else A i').
  Proof.
    intros [rows ptr] A i p (H1 & H2 & H3) Hi [rest Hr]. unfold f_fill. cbn [fst snd] in *.
    pose proof (Full_len i) as HF. pose proof (prefix_len (A i ++ [(φ p)]) rest _ ltac:(rewrite <- app_assoc; exact Hr)) as Hl.
    rewrite length_app in Hl. simpl in Hl.
    destruct (H3 i Hi) as (Hp & Hlr & Hc).
    unfold Rfill. cbn [fst snd].
    split; [rewrite aalength_set; exact H1|]. split; [rewrite alength_set; exact H2|].
    intros i' Hi'. destruct (int_eq_dec i' i) as [-> | Hne].
    - rewrite eqb_refl, aaget_set_same by lia. rewrite aget_set_same by lia.
      rewrite length_app. simpl.
      split; [rewrite phi_add1; [lia | rewrite wB_val; lia]|].
      split; [rewrite alength_set; exact Hlr|].
      intros k Hk. destruct (int_eq_dec k (ptr.[i])) as [-> | Hk'].
      + rewrite aget_set_same by lia. rewrite Hp, Nat2Z.id, app_nth2 by lia.
        rewrite Nat.sub_diag. reflexivity.
      + rewrite aget_set_other by (intro F; apply Hk'; symmetry; exact F).
        pose proof (neq_phi _ _ Hk'). rewrite app_nth1 by lia. apply Hc. lia.
    - replace (i' =? i) with false by (symmetry; apply eqb_false_spec; exact Hne).
      rewrite aaget_set_other by (intro F; apply Hne; symmetry; exact F).
      rewrite aget_set_other by (intro F; apply Hne; symmetry; exact F). apply H3. exact Hi'.
  Qed.

  Lemma alloc_loop_eq : forall cnt mm i rows H,
    alloc_loop cnt mm i rows H =
    match bdec (i <? mm) with
    | left Hi =>
        alloc_loop cnt mm (i + 1) rows.[i <- PArray.make cnt.[i] 0]
          (Acc_inv H (dec_step mm i Hi))
    | right _ => rows
    end.
  Proof. intros. destruct H. reflexivity. Qed.

  Lemma alloc_loop_spec : forall cnt (len : int -> Z),
    (forall i, ((φ i) < m)%Z -> (φ (cnt.[i])) = len i /\ (len i <= 4194303)%Z) ->
    forall z i rows H, gap (PArray.length pats) i = z -> ((φ i) <= m)%Z ->
    (φ (PArray.length rows)) = m ->
    (forall i', ((φ i') < (φ i))%Z -> (φ (PArray.length (rows.[i']))) = len i') ->
    (φ (PArray.length (alloc_loop cnt (PArray.length pats) i rows H))) = m /\
    forall i', ((φ i') < m)%Z ->
      (φ (PArray.length ((alloc_loop cnt (PArray.length pats) i rows H).[i']))) = len i'.
  Proof.
    intros cnt len Hcnt z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros i rows H Hz Hi Hl Hr. rewrite alloc_loop_eq.
    pose proof m_bound as Hm.
    destruct (bdec (i <? PArray.length pats)) as [Hlt | Hge].
    - pose proof (ltb_true _ _ Hlt) as Hlt'. fold m in Hlt'.
      assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by (apply phi_add1; rewrite wB_val; lia).
      apply IH with (y := gap (PArray.length pats) (i + 1));
        [rewrite <- Hz; apply dec_step; exact Hlt | reflexivity | lia | rewrite aalength_set; exact Hl |].
      intros i' Hi'. rewrite Hi1 in Hi'. destruct (int_eq_dec i' i) as [-> | Hne].
      + rewrite aaget_set_same by lia. destruct (Hcnt i Hlt') as [E1 E2].
        rewrite amake_len by lia. exact E1.
      + rewrite aaget_set_other by (intro F; apply Hne; symmetry; exact F).
        apply Hr. pose proof (neq_phi _ _ Hne). lia.
    - apply ltb_false in Hge. fold m in Hge. split; [exact Hl|]. intros i' Hi'. apply Hr. lia.
  Qed.

  End Rows.
End Build.

(* ------------------------------------------------------------------ *)
(* The whole program, on the machine side                              *)
(* ------------------------------------------------------------------ *)

Lemma aamake_len : forall (n : int) (b : array int), ((φ n) <= 4194303)%Z ->
  PArray.length (PArray.make n b) = n.
Proof. intros n b H. exact (alength_make (array int) n b H). Qed.

Lemma Acc_0 : forall pats txt i, Acc_ pats txt 0 i = [].
Proof. reflexivity. Qed.

Lemma impl_core : forall pats txt,
  (forall i, ((φ i) < m pats)%Z -> (0 < plen pats i)%Z) -> (Ptot pats < 4194303)%Z ->
  (m pats < 4194303)%Z -> (Z.of_nat (List.length (T txt)) <= 4194303)%Z ->
  (φ (PArray.length (multimatch_impl pats txt))) = m pats /\
  forall i, ((φ i) < m pats)%Z ->
    (φ (PArray.length ((multimatch_impl pats txt).[i]))) =
      Z.of_nat (List.length (Full pats txt i)) /\
    forall k, ((φ k) < Z.of_nat (List.length (Full pats txt i)))%Z ->
      (φ ((multimatch_impl pats txt).[i].[k])) = nth (Z.to_nat (φ k)) (Full pats txt i) 0%Z.
Proof.
  intros pats txt Hpos HP Hm1 HT.
  pose proof (build_spec pats Hpos HP) as B. cbv zeta in B.
  destruct B as [Hcap [W [Ht [Hlc Hcur]]]].
  unfold multimatch_impl. cbv zeta.
  set (st := rounds _ _ _ _ _) in *.
  set (cap := sums _ _ _ _ _ _) in *.
  set (t := bt st) in *. set (cur := bcur st) in *.
  pose proof (m_bound pats) as Hm.
  pose proof (ti_n _ _ _ Ht) as HN.
  assert (Hmk : forall b : int, PArray.length (PArray.make (fst cap + 1) b) = fst cap + 1)
    by (intros b; apply amake_len; lia).
  assert (Hm1' : (φ (PArray.length pats + 1)) = (m pats + 1)%Z) by (apply phi_add1; unfold m in *; rewrite wB_val; lia).
  (* the pattern lists *)
  assert (HPL0 : PLI pats t (1 + Ptot pats) cur (φ 0) (PArray.make (fst cap + 1) 0)
                   (PArray.make (PArray.length pats + 1) 0)).
  { split; [rewrite Hmk; exact Hcap|].
    split; [rewrite amake_len; [exact Hm1' | rewrite Hm1'; lia]|].
    split; [|split].
    - intros v Hv e. rewrite aget_make. split; [intros F; exfalso; exact (Reach_0 _ _ F)|].
      rewrite phi0. lia.
    - intros e He. rewrite phi0 in He. lia.
    - intros v _. rewrite aget_make, phi0. lia. }
  pose proof (plist_loop_spec pats t _ W cur Ht Hcur Hm1 _ 0 _ _
                (Zwf_well_founded 0 (gap (PArray.length pats) 0)) eq_refl ltac:(rewrite phi0; lia) HPL0)
    as (Hlfp & Hlnp & HP1 & HP2 & _).
  set (pl := plist_loop _ _ _ _ _ _) in *.
  (* the failure and output links *)
  assert (HFI1 : FI pats t (1 + Ptot pats) W cur (φ 1) (PArray.make (fst cap + 1) 0) (PArray.make (fst cap + 1) 0)).
  { split; [rewrite Hmk; exact Hcap|]. split; [rewrite Hmk; exact Hcap|].
    split; [intros x Hx; rewrite phi1 in Hx; lia|].
    intros x Hx. rewrite phi1 in Hx.
    assert (x = 0) by (apply phi_inj; pose proof (phi_bnd x); rewrite phi0; lia). subst x.
    unfold OutOK. rewrite aget_make. split; [rewrite phi0; lia|]. split; [intros F; exfalso; apply F; reflexivity|].
    intros i _ _ Hl. rewrite (ti_root _ _ _ Ht) in Hl. simpl in Hl. lia. }
  pose proof (fail_loop_spec pats t _ W cur Ht Hcur Hm1 (fst pl) (snd pl) HP1 _ 1 _ _
                (Zwf_well_founded 0 (gap (tn t) 1)) eq_refl ltac:(rewrite phi1; lia) HFI1) as HFI.
  set (fo := fail_loop _ _ _ _ _ _ _) in *.
  (* the two text passes *)
  assert (Hn : (φ (PrimString.length txt)) = Z.of_nat (List.length (T txt))) by (unfold T; rewrite pstr_len; reflexivity).
  assert (HL0 : Longest t W (firstn 0 (T txt)) 0).
  { split; [rewrite phi0; lia|]. split; [rewrite (ti_root _ _ _ Ht); apply suffix_nil|].
    intros z _ Hs. apply suffix_length in Hs. simpl in Hs. lia. }
  assert (Hmm : (φ (PArray.length (PArray.make (PArray.length pats) 0))) = m pats)
    by (rewrite amake_len; [reflexivity | unfold m in *; lia]).
  pose proof (scan_spec pats t _ W cur Ht Hcur Hpos Hm1 (fst pl) (snd pl) HP1 HP2 (fst fo) (snd fo) HFI txt
                (array int) (Rcnt pats) f_cnt (Rcnt_ext pats) (Rcnt_f pats txt HT)
                (PrimString.length txt) Hn _ 0 0%nat 0 (PArray.make (PArray.length pats) 0)
                (Zwf_well_founded 0 (gap (PrimString.length txt) 0)) eq_refl phi0 ltac:(lia) HL0
                ltac:(split; [exact Hmm | intros i _; rewrite aget_make, phi0, Acc_0; reflexivity]))
    as [_ Hcnt].
  set (cnt := scan _ _ _ _ _ _ _ _ _ _ _ _ _) in Hcnt.
  assert (Hmr : (φ (PArray.length (PArray.make (PArray.length pats) (PArray.make 0 0)))) = m pats)
    by (rewrite aamake_len; [reflexivity | unfold m in *; lia]).
  pose proof (alloc_loop_spec pats txt cnt (fun i => Z.of_nat (List.length (Full pats txt i)))
                ltac:(intros i Hi; split; [exact (Hcnt i Hi) | pose proof (Full_len pats txt i); lia])
                _ 0 (PArray.make (PArray.length pats) (PArray.make 0 0))
                (Zwf_well_founded 0 (gap (PArray.length pats) 0)) eq_refl ltac:(rewrite phi0; lia)
                Hmr
                ltac:(intros i' Hi'; rewrite phi0 in Hi'; pose proof (phi_bnd i'); lia))
    as [Hlr Hlr2].
  set (rows := alloc_loop _ _ _ _ _) in *.
  assert (HR0 : Rfill pats txt (rows, PArray.make (PArray.length pats) 0) (Acc_ pats txt 0)).
  { split; [exact Hlr|]. split; [exact Hmm|].
    intros i Hi. cbn [fst snd]. rewrite aget_make, phi0, Acc_0. simpl.
    split; [reflexivity|]. split; [exact (Hlr2 i Hi)|]. intros k Hk. pose proof (phi_bnd k). lia. }
  pose proof (scan_spec pats t _ W cur Ht Hcur Hpos Hm1 (fst pl) (snd pl) HP1 HP2 (fst fo) (snd fo) HFI txt
                _ (Rfill pats txt) f_fill (Rfill_ext pats txt) (Rfill_f pats txt HT)
                (PrimString.length txt) Hn _ 0 0%nat 0 _
                (Zwf_well_founded 0 (gap (PrimString.length txt) 0)) eq_refl phi0 ltac:(lia) HL0 HR0)
    as (HF1 & _ & HF3).
  split; [exact HF1|].
  intros i Hi. destruct (HF3 i Hi) as (_ & H2 & H3). split; [exact H2 | exact H3].
Qed.

(* ------------------------------------------------------------------ *)
(* From the machine side to the contract                               *)
(* ------------------------------------------------------------------ *)

(* the character codes of a math string *)
Fixpoint codes (s : String.string) : list Z :=
  match s with
  | String.EmptyString => []
  | String.String a s' => Z.of_N (Ascii.N_of_ascii a) :: codes s'
  end.

Lemma codes_len : forall s, List.length (codes s) = String.length s.
Proof. induction s as [| a s IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma codes_app : forall s1 s2, codes (String.append s1 s2) = codes s1 ++ codes s2.
Proof. induction s1 as [| a s IH]; intros s2; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma codes_nth : forall s k c, String.get k s = Some c ->
  nth k (codes s) 0%Z = Z.of_N (Ascii.N_of_ascii c).
Proof.
  induction s as [| a s IH]; intros k c H; [discriminate|].
  destruct k as [| k]; simpl in H |- *; [injection H as <-; reflexivity | apply IH; exact H].
Qed.

Lemma codes_inj : forall a b, codes a = codes b -> a = b.
Proof.
  induction a as [| x a IH]; intros [| y b] H; simpl in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [|apply IH; exact H2].
  apply N2Z.inj in H1. rewrite <- (Ascii.ascii_N_embedding x), <- (Ascii.ascii_N_embedding y), H1.
  reflexivity.
Qed.

Lemma codes_split : forall s A B, codes s = A ++ B ->
  exists s1 s2, s = String.append s1 s2 /\ codes s1 = A /\ codes s2 = B.
Proof.
  induction s as [| a s IH]; intros A B H.
  - destruct A; [|discriminate]. simpl in H. exists String.EmptyString, String.EmptyString.
    split; [reflexivity|]. split; [reflexivity | exact H].
  - destruct A as [| x A].
    + exists String.EmptyString, (String.String a s). split; [reflexivity|]. split; [reflexivity | exact H].
    + simpl in H. injection H as H1 H2. destruct (IH A B H2) as (s1 & s2 & E & E1 & E2).
      exists (String.String a s1), s2. subst s. split; [reflexivity|]. split; [simpl; rewrite E1, H1; reflexivity | exact E2].
Qed.

Lemma pstr_codes : forall (x : PrimString.string) (s : String.string), repr x s -> pstr x = codes s.
Proof.
  intros x s [Hl Hc]. apply nth_ext with (d := 0%Z) (d' := 0%Z).
  - pose proof (pstr_len x). rewrite codes_len. lia.
  - intros k Hk. pose proof (pstr_len x) as Hlx.
    assert (Hk' : (k < String.length s)%nat) by lia.
    destruct (Hc k Hk') as [c [Hg Hr]].
    rewrite (codes_nth s k c Hg).
    assert (Hb : (Z.of_nat k < wB)%Z) by (pose proof (phi_bnd (PrimString.length x)); lia).
    pose proof (pstr_nth x (of_Z (Z.of_nat k))) as Hn.
    rewrite phi_of_Z in Hn by lia. rewrite Nat2Z.id in Hn. rewrite Hn by lia.
    unfold repr, repr_uint in Hr. pose proof (phi_bnd (PrimString.get x (of_Z (Z.of_nat k)))).
    rewrite <- Hr. lia.
Qed.

Lemma occurs_codes : forall pat txt p, occurs_at pat txt p <->
  exists PRE POST, codes txt = PRE ++ codes pat ++ POST /\ N.of_nat (List.length PRE) = p.
Proof.
  intros pat txt p. split.
  - intros (pre & post & E & Hp). exists (codes pre), (codes post). subst txt.
    rewrite !codes_app. split; [reflexivity|]. rewrite codes_len. exact Hp.
  - intros (PRE & POST & E & Hp).
    destruct (codes_split txt PRE (codes pat ++ POST) E) as (s1 & s2 & E1 & C1 & C2).
    destruct (codes_split s2 (codes pat) POST C2) as (s3 & s4 & E3 & C3 & C4).
    apply codes_inj in C3. subst. exists s1, s4. split; [reflexivity|].
    unfold slen. rewrite <- codes_len. reflexivity.
Qed.

Lemma list_occ : forall (P Tl : list Z) (p : N), P <> [] ->
  ((exists j, (j < List.length Tl)%nat /\ suffix P (firstn (S j) Tl) /\
              p = Z.to_N (Z.of_nat j + 1 - Z.of_nat (List.length P))) <->
   exists PRE POST, Tl = PRE ++ P ++ POST /\ N.of_nat (List.length PRE) = p).
Proof.
  intros P Tl p HP. split.
  - intros (j & Hj & [Z0 HZ] & Hp). exists Z0, (skipn (S j) Tl).
    assert (Hl : List.length (firstn (S j) Tl) = S j) by (rewrite length_firstn; lia).
    split.
    + rewrite <- (firstn_skipn (S j) Tl) at 1. rewrite HZ, app_assoc. reflexivity.
    + rewrite HZ, length_app in Hl. rewrite Hp. lia.
  - intros (PRE & POST & E & Hp).
    assert (HlP : (1 <= List.length P)%nat) by (destruct P; [contradiction | simpl; lia]).
    exists (List.length PRE + List.length P - 1)%nat. subst Tl. rewrite !length_app.
    split; [lia|]. split.
    + exists PRE. replace (S (List.length PRE + List.length P - 1)) with (List.length (PRE ++ P))
        by (rewrite length_app; lia).
      rewrite app_assoc, firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
    + rewrite <- Hp. lia.
Qed.

Lemma filter_seq_sorted : forall (f : nat -> bool) n a t u,
  (t < u < List.length (filter f (seq a n)))%nat ->
  (nth t (filter f (seq a n)) 0%nat < nth u (filter f (seq a n)) 0%nat)%nat.
Proof.
  intros f n. induction n as [| n IH]; intros a t u Htu; simpl in *; [lia|].
  destruct (f a) eqn:Ef; simpl in Htu |- *.
  - destruct t as [| t]; destruct u as [| u]; try lia.
    + assert (Hin : In (nth u (filter f (seq (S a) n)) 0%nat) (filter f (seq (S a) n))) by (apply nth_In; lia).
      apply filter_In in Hin as [Hin _]. apply in_seq in Hin. lia.
    + apply IH. lia.
  - apply IH. exact Htu.
Qed.

Lemma map_sorted : forall (L : list nat) (g : nat -> N),
  (forall t u, (t < u < List.length L)%nat -> (nth t L 0%nat < nth u L 0%nat)%nat) ->
  (forall a b, In a L -> In b L -> (a < b)%nat -> (g a < g b)%N) ->
  forall t u, (t < u < List.length L)%nat -> (nth t (map g L) 0%N < nth u (map g L) 0%N)%N.
Proof.
  intros L g HL Hg t u Htu.
  rewrite (nth_indep (map g L) 0%N (g 0%nat)) by (rewrite length_map; lia).
  rewrite (nth_indep (map g L) 0%N (g 0%nat) (n := u)) by (rewrite length_map; lia).
  rewrite !map_nth. apply Hg; [apply nth_In; lia | apply nth_In; lia | apply HL; exact Htu].
Qed.

Lemma zsum_ext_in : forall f g l, (forall i, In i l -> f i = g i) -> zsum f l = zsum g l.
Proof.
  intros f g l H. induction l as [| a l IH]; simpl; [reflexivity|].
  rewrite IH by (intros i Hi; apply H; right; exact Hi). rewrite H by (left; reflexivity). reflexivity.
Qed.

Lemma zsum_iseq_list : forall (l : list String.string) n, (n <= List.length l)%nat ->
  (Z.of_nat n < wB)%Z ->
  zsum (fun i => Z.of_nat (String.length (nth (Z.to_nat (φ i)) l String.EmptyString))) (iseq (Z.of_nat n))
  = Z.of_nat (list_sum (map String.length (firstn n l))).
Proof.
  intros l n. induction n as [| n IH]; intros Hn Hw; [reflexivity|].
  replace (Z.of_nat (S n)) with (Z.of_nat n + 1)%Z by lia.
  rewrite iseq_S, zsum_app by lia. rewrite IH by lia.
  rewrite (firstn_snoc_gen l n String.EmptyString) by lia.
  rewrite map_app, list_sum_app. unfold zsum at 1. cbn [fold_right map list_sum].
  rewrite phi_of_Z by lia. rewrite Nat2Z.id. lia.
Qed.

Lemma zsum_one : forall l, zsum (fun _ => 1%Z) l = Z.of_nat (List.length l).
Proof.
  induction l as [| a l IH]; [reflexivity|].
  change (zsum (fun _ => 1%Z) (a :: l)) with (1 + zsum (fun _ => 1%Z) l)%Z.
  rewrite IH. cbn [List.length]. lia.
Qed.

Lemma nth_map_seq : forall {A} (f : nat -> A) n k d, (k < n)%nat -> nth k (map f (seq 0 n)) d = f k.
Proof.
  intros A f n k d Hk. rewrite nth_indep with (d' := f 0%nat) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

Lemma multimatch_impl_correct : forall (pats : list String.string) (txt : String.string)
    (xp : array PrimString.string) (xt : PrimString.string),
  valid_input pats txt -> repr xp pats -> repr xt txt ->
  exists rows : list (list N), repr (multimatch_impl xp xt) rows /\ multimatch_spec pats txt rows.
Proof.
  intros pats txt xp xt Hv Hxp Hxt.
  destruct Hv as [Hvp Hvtot Hvt].
  pose proof Hxp as [Hlp Hcp].
  assert (Hm : m xp = Z.of_nat (List.length pats)) by (unfold m; symmetry; exact Hlp).
  pose proof (m_bound xp) as Hmb.
  assert (Hpw : forall k, (k < List.length pats)%nat ->
            pw xp (of_Z (Z.of_nat k)) = codes (nth k pats String.EmptyString)).
  { intros k Hk. destruct (Hcp k Hk) as [s [Hs Hr]]. rewrite (nth_error_nth _ _ _ Hs).
    unfold pw. apply pstr_codes. exact Hr. }
  assert (Hpw' : forall i, ((φ i) < m xp)%Z ->
            pw xp i = codes (nth (Z.to_nat (φ i)) pats String.EmptyString)).
  { intros i Hi. rewrite <- Hpw by lia. f_equal. apply phi_inj. rewrite phi_of_Z.
    - pose proof (phi_bnd i). lia.
    - pose proof (phi_bnd i). rewrite wB_val. lia. }
  assert (Hplen : forall i, ((φ i) < m xp)%Z ->
            plen xp i = Z.of_nat (String.length (nth (Z.to_nat (φ i)) pats String.EmptyString))).
  { intros i Hi. rewrite <- plen_len, Hpw', codes_len by exact Hi. reflexivity. }
  assert (HT : T xt = codes txt) by (unfold T; apply pstr_codes; exact Hxt).
  assert (Hpos : forall i, ((φ i) < m xp)%Z -> (0 < plen xp i)%Z).
  { intros i Hi. rewrite Hplen by exact Hi. rewrite Forall_forall in Hvp.
    assert (Hin : In (nth (Z.to_nat (φ i)) pats String.EmptyString) pats) by (apply nth_In; lia).
    pose proof (Hvp _ Hin) as H1. unfold slen in H1. lia. }
  assert (HPt : Ptot xp = Z.of_nat (list_sum (map String.length pats))).
  { unfold Ptot.
    rewrite (zsum_ext_in _ (fun i => Z.of_nat (String.length (nth (Z.to_nat (φ i)) pats String.EmptyString)))).
    - rewrite Hm, zsum_iseq_list, firstn_all; [reflexivity | lia | rewrite wB_val; lia].
    - intros i Hi. apply iseq_In in Hi; [| rewrite wB_val; lia]. apply Hplen. exact Hi. }
  unfold total_length in Hvtot.
  assert (HmP : (m xp <= Ptot xp)%Z).
  { unfold Ptot.
    assert (E1 : zsum (fun _ => 1%Z) (iseq (m xp)) = m xp) by (rewrite zsum_one, iseq_len; lia).
    rewrite <- E1 at 1. apply zsum_le. intros i Hi.
    apply iseq_In in Hi; [| rewrite wB_val; lia]. pose proof (Hpos i Hi). lia. }
  assert (HTl : (Z.of_nat (List.length (T xt)) <= 4194303)%Z)
    by (rewrite HT, codes_len; unfold slen in Hvt; lia).
  destruct (impl_core xp xt Hpos ltac:(lia) ltac:(lia) HTl) as [HR1 HR2].
  set (res := multimatch_impl xp xt) in *.
  exists (map (fun k => map Z.to_N (Full xp xt (of_Z (Z.of_nat k)))) (seq 0 (List.length pats))).
  split.
  - split.
    + rewrite length_map, length_seq. rewrite <- Hm. symmetry. exact HR1.
    + intros k Hk. rewrite length_map, length_seq in Hk.
      exists (map Z.to_N (Full xp xt (of_Z (Z.of_nat k)))). split.
      * rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec k (List.length pats)); [reflexivity | lia].
      * assert (Hi : ((φ (of_Z (Z.of_nat k))) < m xp)%Z) by (rewrite phi_of_Z; [lia | rewrite wB_val; lia]).
        destruct (HR2 _ Hi) as [Hl Hc].
        split.
        -- rewrite length_map. symmetry. exact Hl.
        -- intros k' Hk'. rewrite length_map in Hk'.
           exists (Z.to_N (nth k' (Full xp xt (of_Z (Z.of_nat k))) 0%Z)). split.
           ++ rewrite nth_error_map. rewrite (nth_error_nth' _ 0%Z) by exact Hk'. reflexivity.
           ++ unfold repr, repr_uint. f_equal.
              assert (Hk2 : ((φ (of_Z (Z.of_nat k'))) < Z.of_nat (List.length (Full xp xt (of_Z (Z.of_nat k)))))%Z)
                by (rewrite phi_of_Z; [lia | rewrite wB_val; pose proof (Full_len xp xt (of_Z (Z.of_nat k))); lia]).
              pose proof (Hc _ Hk2) as Hc2.
              rewrite phi_of_Z, Nat2Z.id in Hc2 by (rewrite wB_val; pose proof (Full_len xp xt (of_Z (Z.of_nat k))); lia).
              exact Hc2.
  - split.
    + unfold len. rewrite length_map, length_seq. reflexivity.
    + intros i Hi. unfold len in Hi.
      set (k := N.to_nat i).
      assert (Hk : (k < List.length pats)%nat) by lia.
      unfold get_row, get_pattern. fold k. rewrite nth_map_seq by exact Hk.
      set (ii := of_Z (Z.of_nat k)).
      assert (Hii : ((φ ii) < m xp)%Z) by (unfold ii; rewrite phi_of_Z; [lia | rewrite wB_val; lia]).
      set (pat := nth k pats String.EmptyString).
      assert (HP : pw xp ii = codes pat) by (apply Hpw; exact Hk).
      assert (HPl : plen xp ii = Z.of_nat (List.length (codes pat))) by (rewrite <- HP; symmetry; apply plen_len).
      assert (HPne : codes pat <> []).
      { intro E. pose proof (Hpos ii Hii). rewrite HPl, E in H. simpl in H. lia. }
      unfold Full, Acc_. rewrite map_map.
      set (L := filter (occb xp xt ii) (seq 0 (List.length (T xt)))).
      assert (HLpos : forall a, In a L -> (0 <= pos xp a ii)%Z).
      { intros a Ha. apply filter_In in Ha as [_ Ha]. unfold occb in Ha. apply suffixb_spec in Ha.
        apply suffix_length in Ha. rewrite length_firstn in Ha. unfold pos. rewrite HPl, <- HP. lia. }
      split.
      * unfold ascending, get_list_N, len. rewrite length_map. intros t u Htu.
        apply map_sorted; [ | | lia].
        -- intros t' u' Htu'. apply filter_seq_sorted. exact Htu'.
        -- intros a b Ha Hb Hab. pose proof (HLpos a Ha). pose proof (HLpos b Hb).
           apply Z2N.inj_lt; [lia | lia |]. unfold pos. lia.
      * intros p. rewrite in_map_iff, occurs_codes, <- (list_occ (codes pat) (codes txt) p HPne).
        split.
        -- intros (j & Hgj & Hj). unfold L in Hj. apply filter_In in Hj as [Hj1 Hj2]. apply in_seq in Hj1.
           unfold occb in Hj2. apply suffixb_spec in Hj2. rewrite HP, HT in Hj2.
           exists j. split; [rewrite <- HT; lia|]. split; [exact Hj2|].
           rewrite <- Hgj. unfold pos. rewrite HPl. reflexivity.
        -- intros (j & Hj & Hs & Hp). exists j. split.
           ++ rewrite Hp. unfold pos. rewrite HPl. reflexivity.
           ++ unfold L. apply filter_In. split; [apply in_seq; rewrite HT; lia|].
              unfold occb. apply suffixb_spec. rewrite HP, HT. exact Hs.
Qed.

Definition multimatch_correct :
  forall (pats : list String.string) (txt : String.string)
         (xp : array PrimString.string) (xt : PrimString.string),
  valid_input pats txt -> repr xp pats -> repr xt txt ->
  exists rows : list (list N),
    repr (multimatch xp xt) rows /\ multimatch_spec pats txt rows
  := multimatch_impl_correct.
