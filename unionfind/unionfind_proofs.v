(* Correctness proofs for unionfind_implem.v. *)
(* Implementation of unionfind (unionfind.spec): disjoint-set union with
   union by rank and full path compression, over one left-to-right scan of
   the operations.

   Code.  [run_ops n is_union a b] builds the parent array [par] (cell i
   holds i) and a rank array [rk] (all 0), both flat arrays of n cells, and
   an answer array of Q cells (all false).  Operation k finds the roots ra
   of a[k] and rb of b[k] (each [find] compresses the path it walks: every
   node on it is re-pointed at the root); a union links the root of lower
   rank under the other one (ties: ra under rb, rank of rb + 1), a query
   writes [ra =? rb] into answer cell k.  All three arrays are threaded
   linearly; [find] is recursive (depth = length of the path, O(log n)
   under union by rank) and returns the root with the new parent array.

   Termination.  [init_loop] and [scan] recurse on an erased
   [Acc (Zwf 0) (gap m i)] as in template/polymul1.  [find] recurses on an
   erased [Acc (R par) x], where [R par y x] says y is the parent of the
   non-root x: the scan carries, as an erased argument, the proof
   [wf_par par] that every element is accessible (no parent cycle), and
   re-establishes it after every find and every link from Prop lemmas
   ([find_wf], [link_wf]).  No runtime guard, no fuel, no nat.

   Proof.  A root path [path par x r] (follow parents from x until the
   fixpoint r); [sameroot par x y] when x and y reach the same root.  The
   scan invariant [Inv k par] says: par has n cells all pointing into
   [0, n); every union among the first k operations joined its two
   elements (they have the same root); two elements with the same root are
   connected by the first k operations.  The converse direction of the
   query answer is an induction on [connected]. *)

From Unionfind.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Relations Transitive_Closure.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

From Unionfind Require Export unionfind_implem.
Open Scope uint63_scope.
Open Scope array_scope.


(* ------------------------------------------------------------------ *)
(* Uint63 / PArray plumbing                                            *)
(* ------------------------------------------------------------------ *)

Lemma max_length_val : (φ PArray.max_length) = 4194303%Z.
Proof. reflexivity. Qed.

Lemma alength_bound : forall A (t : array A), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros A t. pose proof (leb_length A t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

Lemma alength_make : forall (n : int) (b : int),
  PArray.length (PArray.make n b)
  = if n <=? PArray.max_length then n else PArray.max_length.
Proof. intros n b. exact (length_make int n b). Qed.

Lemma bget_set_same : forall (t : array bool) (i : int) (b : bool),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same bool t i b H). Qed.

Lemma bget_set_other : forall (t : array bool) (i j : int) (b : bool),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other bool t i j b H). Qed.

Lemma blength_set : forall (t : array bool) (i : int) (b : bool),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set bool t i b). Qed.

Lemma blength_make : forall (n : int) (b : bool),
  PArray.length (PArray.make n b)
  = if n <=? PArray.max_length then n else PArray.max_length.
Proof. intros n b. exact (length_make bool n b). Qed.

Definition toN (x : int) : N := Z.to_N (φ x).

Lemma toN_inj : forall x y, toN x = toN y -> x = y.
Proof.
  intros x y H. unfold toN in H. apply to_Z_inj.
  pose proof (to_Z_bounded x). pose proof (to_Z_bounded y). lia.
Qed.

Definition sameroot (p : array int) (x y : int) : Prop :=
  exists r, path p x r /\ path p y r.

Lemma path_det : forall p x r1 r2, path p x r1 -> path p x r2 -> r1 = r2.
Proof.
  intros p x r1 r2 H1. revert r2. induction H1 as [x Hx | x r Hne H IH];
    intros r2 H2.
  - symmetry. exact (path_of_root p x r2 Hx H2).
  - inversion H2 as [x' Hx' | x' r' Hne' Hr']; subst.
    + contradiction.
    + apply IH. exact Hr'.
Qed.

Lemma path_exists : forall p x, Acc (R p) x -> exists r, path p x r.
Proof.
  intros p x A. induction A as [x _ IH].
  destruct (p.[x] =? x) eqn:E.
  - apply eqb_spec in E. exists x. apply path_root. exact E.
  - destruct (IH p.[x] (find_step p x E)) as [r Hr].
    exists r. apply path_step; [apply eqb_false_spec; exact E | exact Hr].
Qed.

Lemma path_range : forall p (nn : Z),
  (forall y, ((φ y) < nn)%Z -> ((φ (p.[y])) < nn)%Z) ->
  forall x r, path p x r -> ((φ x) < nn)%Z -> ((φ r) < nn)%Z.
Proof.
  intros p nn B x r H. induction H as [x Hx | x r Hne H IH]; intros Hl; auto.
Qed.

Lemma sameroot_sym : forall p x y, sameroot p x y -> sameroot p y x.
Proof. intros p x y (r & H1 & H2). exists r. auto. Qed.

Lemma sameroot_trans : forall p x y z,
  sameroot p x y -> sameroot p y z -> sameroot p x z.
Proof.
  intros p x y z (r & H1 & H2) (r' & H3 & H4).
  rewrite (path_det p y r r' H2 H3) in H1. exists r'. auto.
Qed.

Lemma sameroot_refl : forall p x, wf_par p -> sameroot p x x.
Proof. intros p x W. destruct (path_exists p x (W x)) as [r Hr]. exists r. auto. Qed.

(* x reaches the root r *)
Lemma sameroot_root : forall p x r, path p x r -> sameroot p x r.
Proof.
  intros p x r H. exists r. split; [exact H|].
  apply path_root. exact (path_fix p x r H).
Qed.

Lemma sameroot_to_root : forall p x r, p.[r] = r -> sameroot p x r -> path p x r.
Proof.
  intros p x r Hr (r' & H1 & H2). rewrite (path_of_root p r r' Hr H2) in H1. exact H1.
Qed.

Lemma compat_path : forall p p', compat p p' ->
  forall y r, path p y r -> path p' y r.
Proof.
  intros p p' C y r H. induction H as [x Hx | x r Hne H IH].
  - apply path_root. exact (compat_root p p' x C Hx).
  - destruct (C x) as [E | P].
    + apply path_step; rewrite E; [exact Hne | exact IH].
    + assert (Hxr : path p x r) by (apply path_step; auto).
      pose proof (path_det p x _ _ P Hxr) as Er.
      pose proof (path_fix p _ _ H) as Fr.
      assert (Nr : r <> x) by (intro F; rewrite F in Fr; exact (Hne Fr)).
      apply path_step; rewrite Er; [exact Nr|].
      apply path_root. exact (compat_root p p' r C Fr).
Qed.

Lemma compat_path_inv : forall p p', wf_par p -> compat p p' ->
  forall y r, path p' y r -> path p y r.
Proof.
  intros p p' W C y r H.
  destruct (path_exists p y (W y)) as [r0 H0].
  rewrite (path_det p' y r r0 H (compat_path p p' C y r0 H0)). exact H0.
Qed.

Lemma compat_range : forall p p' (nn : Z), compat p p' ->
  (forall y, ((φ y) < nn)%Z -> ((φ (p.[y])) < nn)%Z) ->
  (forall y, ((φ y) < nn)%Z -> ((φ (p'.[y])) < nn)%Z).
Proof.
  intros p p' nn C B y Hy. destruct (C y) as [E | P].
  - rewrite E. apply B. exact Hy.
  - exact (path_range p nn B y _ P Hy).
Qed.

Lemma compat_sameroot : forall p p', wf_par p -> compat p p' ->
  forall x y, sameroot p x y <-> sameroot p' x y.
Proof.
  intros p p' W C x y. split; intros (r & H1 & H2); exists r.
  - split; apply (compat_path p p' C); assumption.
  - split; apply (compat_path_inv p p' W C); assumption.
Qed.

Lemma scan_eq : forall xu xa xb q k par rk out W H,
  scan xu xa xb q k par rk out W H =
  match bdec (k <? q) with
  | left Hk =>
      let a := xa.[k] in
      let b := xb.[k] in
      let fa := find par a (W a) in
      let Wa := find_wf par a (W a) W in
      let fb := find (snd fa) b (Wa b) in
      let Wb := find_wf (snd fa) b (Wa b) Wa in
      if xu.[k] then
        let l := link (snd fb) rk (fst fa) (fst fb) in
        scan xu xa xb q (k + 1) (fst l) (snd l) out
          (link_wf (snd fb) rk (fst fa) (fst fb) Wb
             (find_keeps_root (snd fa) b (Wa b) (fst fa) (find_root par a (W a)))
             (find_root (snd fa) b (Wa b)))
          (Acc_inv H (dec_step q k Hk))
      else
        scan xu xa xb q (k + 1) (snd fb) rk out.[k <- fst fa =? fst fb] Wb
          (Acc_inv H (dec_step q k Hk))
  | right _ => out
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Prop side: linking two roots                                        *)
(* ------------------------------------------------------------------ *)

(* The root r of p becomes, after p.[u <- v], relink u v r. *)
Definition relink (u v r : int) : int := if r =? u then v else r.

Lemma link_path : forall p u v, p.[u] = u -> p.[v] = v -> u <> v ->
  (u <? PArray.length p) = true ->
  forall y r, path p y r -> path p.[u <- v] y (relink u v r).
Proof.
  intros p u v Hu Hv Huv Hl y r H. induction H as [x Hx | x r Hne H IH].
  - unfold relink. destruct (x =? u) eqn:E.
    + apply eqb_spec in E. subst x. apply path_step.
      * rewrite aget_set_same by exact Hl. intro F. apply Huv. symmetry. exact F.
      * rewrite aget_set_same by exact Hl. apply path_root.
        rewrite aget_set_other by exact Huv. exact Hv.
    + apply eqb_false_spec in E. apply path_root.
      rewrite aget_set_other by (intro F; apply E; symmetry; exact F). exact Hx.
  - assert (Hxu : u <> x) by (intro F; rewrite <- F in Hne; exact (Hne Hu)).
    apply path_step; rewrite aget_set_other by exact Hxu; [exact Hne | exact IH].
Qed.

Lemma link_sameroot1 : forall p u v, p.[u] = u -> p.[v] = v -> u <> v ->
  (u <? PArray.length p) = true ->
  forall x y, sameroot p x y -> sameroot p.[u <- v] x y.
Proof.
  intros p u v Hu Hv Huv Hl x y (r & P1 & P2). exists (relink u v r).
  split; apply link_path; assumption.
Qed.

Lemma link_sameroot2 : forall p u v, p.[u] = u -> p.[v] = v -> u <> v ->
  (u <? PArray.length p) = true -> sameroot p.[u <- v] u v.
Proof.
  intros p u v Hu Hv Huv Hl. exists v. split.
  - pose proof (link_path p u v Hu Hv Huv Hl u u (path_root p u Hu)) as P.
    unfold relink in P. rewrite eqb_refl in P. exact P.
  - pose proof (link_path p u v Hu Hv Huv Hl v v (path_root p v Hv)) as P.
    unfold relink in P.
    assert (E : (v =? u) = false) by (apply eqb_false_spec; intro F; apply Huv; symmetry; exact F).
    rewrite E in P. exact P.
Qed.

Lemma link_sameroot3 : forall p u v, wf_par p -> p.[u] = u -> p.[v] = v -> u <> v ->
  (u <? PArray.length p) = true ->
  forall x y, sameroot p.[u <- v] x y ->
  sameroot p x y \/ (sameroot p x u /\ sameroot p y v) \/
  (sameroot p x v /\ sameroot p y u).
Proof.
  intros p u v W Hu Hv Huv Hl x y (r & Q1 & Q2).
  destruct (path_exists p x (W x)) as [rx Px].
  destruct (path_exists p y (W y)) as [ry Py].
  pose proof (path_det _ _ _ _ Q1 (link_path p u v Hu Hv Huv Hl x rx Px)) as E1.
  pose proof (path_det _ _ _ _ Q2 (link_path p u v Hu Hv Huv Hl y ry Py)) as E2.
  rewrite E1 in E2. unfold relink in E2.
  destruct (rx =? u) eqn:A; destruct (ry =? u) eqn:B.
  - apply eqb_spec in A, B. subst rx ry. left. exists u. auto.
  - apply eqb_spec in A. subst rx. subst ry. right. left.
    split; apply sameroot_root; assumption.
  - apply eqb_spec in B. subst ry. subst rx. right. right.
    split; apply sameroot_root; assumption.
  - subst ry. left. exists rx. auto.
Qed.

(* ------------------------------------------------------------------ *)
(* Prop side: the initial parent array                                 *)
(* ------------------------------------------------------------------ *)

Lemma init_spec : forall nn, ((φ nn) <= 4194303)%Z ->
  forall z i p H, gap nn i = z -> PArray.length p = nn -> ((φ i) <= (φ nn))%Z ->
  (forall y, ((φ y) < (φ i))%Z -> p.[y] = y) ->
  PArray.length (init_loop nn i p H) = nn /\
  forall y, ((φ y) < (φ nn))%Z -> (init_loop nn i p H).[y] = y.
Proof.
  intros nn Hnn z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i p H Hz Hl Hi Hc. rewrite init_loop_eq.
  destruct (bdec (i <? nn)) as [Hin | Hin].
  - pose proof Hin as Hin'. rewrite ltb_spec in Hin'.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    eapply IH; [ | reflexivity | rewrite alength_set; exact Hl | lia | ].
    + rewrite <- Hz. apply dec_step. exact Hin.
    + intros y Hy. destruct (Z.eq_dec (φ y) (φ i)) as [E | E].
      * assert (y = i) by (apply to_Z_inj; exact E). subst y.
        apply aget_set_same. rewrite Hl. exact Hin.
      * rewrite aget_set_other by (intro F; apply E; rewrite F; reflexivity).
        apply Hc. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hin.
    split; [exact Hl|]. intros y Hy. apply Hc. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Prop side: the scan                                                 *)
(* ------------------------------------------------------------------ *)

Section Correct.

Variables (n : N) (is_union : list bool) (elt_a elt_b : list N).
Variables (xn : int) (xu : array bool) (xa xb : array int).
Hypothesis Hv : valid_input n is_union elt_a elt_b.
Hypothesis Hn : repr (xn : uint) n.
Hypothesis Hu : repr xu is_union.
Hypothesis Ha : repr (xa : array uint) elt_a.
Hypothesis Hb : repr (xb : array uint) elt_b.

Local Notation conn := (connected is_union elt_a elt_b).
Local Notation q := (PArray.length xu).

Lemma xn_val : (φ xn) = Z.of_N n.
Proof. pose proof Hn as H. unfold repr, repr_uint in H. pose proof (to_Z_bounded xn). lia. Qed.

Lemma xn_bounds : (1 <= (φ xn) <= 1000000)%Z.
Proof. pose proof (vi_n _ _ _ _ Hv). rewrite xn_val. lia. Qed.

Lemma q_val : (φ q) = Z.of_nat (List.length is_union).
Proof. destruct Hu as [Hl _]. symmetry. exact Hl. Qed.

Lemma q_bound : ((φ q) <= 1000000)%Z.
Proof. pose proof (vi_q _ _ _ _ Hv). unfold len in *. rewrite q_val. lia. Qed.

Lemma lenA : List.length elt_a = List.length is_union.
Proof. pose proof (vi_a_length _ _ _ _ Hv). unfold len in *. lia. Qed.

Lemma lenB : List.length elt_b = List.length is_union.
Proof. pose proof (vi_b_length _ _ _ _ Hv). unfold len in *. lia. Qed.

Lemma getU : forall j, ((φ j) < (φ q))%Z -> get_list_bool is_union (toN j) = xu.[j].
Proof.
  intros j Hj. pose proof (to_Z_bounded j). rewrite q_val in Hj.
  destruct Hu as [_ Hc].
  destruct (Hc (Z.to_nat (φ j)) ltac:(lia)) as (m & Hm & Hr).
  unfold repr, repr_bool in Hr.
  rewrite Z2Nat.id in Hr by lia. rewrite of_to_Z in Hr.
  unfold get_list_bool, toN. rewrite Z_N_nat.
  erewrite nth_error_nth; [|exact Hm]. symmetry. exact Hr.
Qed.

Lemma getA : forall j, ((φ j) < (φ q))%Z -> get_list_N elt_a (toN j) = toN (xa.[j]).
Proof.
  intros j Hj. pose proof (to_Z_bounded j). rewrite q_val, <- lenA in Hj.
  destruct Ha as [_ Hc].
  destruct (Hc (Z.to_nat (φ j)) ltac:(lia)) as (m & Hm & Hr).
  unfold repr, repr_uint in Hr.
  rewrite Z2Nat.id in Hr by lia. rewrite of_to_Z in Hr.
  unfold get_list_N, toN. rewrite Z_N_nat.
  erewrite nth_error_nth; [|exact Hm]. symmetry. exact Hr.
Qed.

Lemma getB : forall j, ((φ j) < (φ q))%Z -> get_list_N elt_b (toN j) = toN (xb.[j]).
Proof.
  intros j Hj. pose proof (to_Z_bounded j). rewrite q_val, <- lenB in Hj.
  destruct Hb as [_ Hc].
  destruct (Hc (Z.to_nat (φ j)) ltac:(lia)) as (m & Hm & Hr).
  unfold repr, repr_uint in Hr.
  rewrite Z2Nat.id in Hr by lia. rewrite of_to_Z in Hr.
  unfold get_list_N, toN. rewrite Z_N_nat.
  erewrite nth_error_nth; [|exact Hm]. symmetry. exact Hr.
Qed.

Lemma toN_lt_len : forall j, ((φ j) < (φ q))%Z -> (toN j < len is_union)%N.
Proof.
  intros j Hj. pose proof (to_Z_bounded j). rewrite q_val in Hj.
  unfold toN, len. lia.
Qed.

Lemma rangeA : forall j, ((φ j) < (φ q))%Z -> ((φ (xa.[j])) < (φ xn))%Z.
Proof.
  intros j Hj. pose proof (vi_a_range _ _ _ _ Hv (toN j) (toN_lt_len j Hj)) as H.
  rewrite getA in H by exact Hj. unfold toN in H. rewrite xn_val.
  pose proof (to_Z_bounded (xa.[j])). lia.
Qed.

Lemma rangeB : forall j, ((φ j) < (φ q))%Z -> ((φ (xb.[j])) < (φ xn))%Z.
Proof.
  intros j Hj. pose proof (vi_b_range _ _ _ _ Hv (toN j) (toN_lt_len j Hj)) as H.
  rewrite getB in H by exact Hj. unfold toN in H. rewrite xn_val.
  pose proof (to_Z_bounded (xb.[j])). lia.
Qed.

Lemma toN_succ : forall k, ((φ k) < (φ q))%Z -> toN (k + 1) = (toN k + 1)%N.
Proof.
  intros k Hk. pose proof q_bound. pose proof (to_Z_bounded k).
  assert (E : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
  unfold toN. rewrite E. lia.
Qed.

Lemma conn_mono : forall k a b, conn k a b -> forall k', (k <= k')%N -> conn k' a b.
Proof.
  intros k a b H. induction H as [a | m Hm Hum | a b _ IH | a b c _ IH1 _ IH2];
    intros k' Hk'.
  - apply conn_refl.
  - apply conn_union; [lia | exact Hum].
  - apply conn_sym. apply IH. exact Hk'.
  - apply (conn_trans _ _ _ _ a b c); [apply IH1 | apply IH2]; exact Hk'.
Qed.

(* The scan invariant after the first k operations. *)
Definition Inv (k : int) (p : array int) : Prop :=
  PArray.length p = xn /\
  (forall y, ((φ y) < (φ xn))%Z -> ((φ (p.[y])) < (φ xn))%Z) /\
  (forall m, ((φ m) < (φ k))%Z -> xu.[m] = true -> sameroot p (xa.[m]) (xb.[m])) /\
  (forall x y, ((φ x) < (φ xn))%Z -> ((φ y) < (φ xn))%Z -> sameroot p x y ->
     conn (toN k) (toN x) (toN y)).

(* The answers of the first k operations. *)
Definition OutInv (k : int) (out : array bool) : Prop :=
  PArray.length out = q /\
  forall j, ((φ j) < (φ k))%Z -> xu.[j] = false ->
    (out.[j] = true <->
     conn (toN j) (get_list_N elt_a (toN j)) (get_list_N elt_b (toN j))).

Lemma inv_transfer : forall k p p', wf_par p -> compat p p' ->
  PArray.length p' = PArray.length p -> Inv k p -> Inv k p'.
Proof.
  intros k p p' W C L (L0 & B & C1 & C2).
  split; [rewrite L; exact L0|]. split; [exact (compat_range p p' _ C B)|]. split.
  - intros m Hm Hum. apply (compat_sameroot p p' W C). apply C1; assumption.
  - intros x y Hx Hy S. apply C2; [exact Hx | exact Hy|].
    apply (compat_sameroot p p' W C). exact S.
Qed.

(* Two elements connected by the first k operations. *)
Definition Srel (p : array int) (a b : N) : Prop :=
  a = b \/ exists x y, ((φ x) < (φ xn))%Z /\ ((φ y) < (φ xn))%Z /\
                       toN x = a /\ toN y = b /\ sameroot p x y.

Lemma conn_to_S : forall k p, Inv k p -> ((φ k) <= (φ q))%Z ->
  forall a b, conn (toN k) a b -> Srel p a b.
Proof.
  intros k p (_ & _ & C1 & _) Hk a b Hc.
  induction Hc as [a | m Hm Hum | a b _ IH | a b c _ IH1 _ IH2].
  - left. reflexivity.
  - pose proof q_bound. pose proof (to_Z_bounded k).
    set (j := of_Z (Z.of_N m)).
    assert (Hj : (φ j) = Z.of_N m).
    { unfold j. rewrite of_Z_spec. apply Z.mod_small. unfold toN in Hm. lia. }
    assert (Hjq : ((φ j) < (φ q))%Z) by (unfold toN in Hm; lia).
    assert (Tj : toN j = m) by (unfold toN; rewrite Hj; lia).
    right. exists (xa.[j]), (xb.[j]).
    split; [exact (rangeA j Hjq)|]. split; [exact (rangeB j Hjq)|].
    split; [rewrite <- (getA j Hjq), Tj; reflexivity|].
    split; [rewrite <- (getB j Hjq), Tj; reflexivity|].
    apply C1; [unfold toN in Hm; lia|].
    rewrite <- (getU j Hjq), Tj. exact Hum.
  - destruct IH as [E | (x & y & Hx & Hy & Ex & Ey & S)].
    + left. symmetry. exact E.
    + right. exists y, x. repeat split; auto. apply sameroot_sym. exact S.
  - destruct IH1 as [E1 | (x1 & y1 & Hx1 & Hy1 & Ex1 & Ey1 & S1)];
    destruct IH2 as [E2 | (x2 & y2 & Hx2 & Hy2 & Ex2 & Ey2 & S2)].
    + left. rewrite E1. exact E2.
    + right. exists x2, y2. repeat split; auto. rewrite Ex2. symmetry. exact E1.
    + right. exists x1, y1. repeat split; auto. rewrite Ey1. exact E2.
    + right. exists x1, y2. repeat split; auto.
      assert (y1 = x2) by (apply toN_inj; rewrite Ey1, Ex2; reflexivity). subst x2.
      exact (sameroot_trans p _ _ _ S1 S2).
Qed.

Lemma query_correct : forall k p ra rb, Inv k p -> wf_par p -> ((φ k) < (φ q))%Z ->
  path p (xa.[k]) ra -> path p (xb.[k]) rb ->
  ((ra =? rb) = true <->
   conn (toN k) (get_list_N elt_a (toN k)) (get_list_N elt_b (toN k))).
Proof.
  intros k p ra rb I W Hk Pa Pb.
  rewrite (getA k Hk), (getB k Hk).
  pose proof (rangeA k Hk). pose proof (rangeB k Hk).
  split.
  - intros E. apply eqb_spec in E. subst rb.
    destruct I as (_ & _ & _ & C2). apply C2; auto. exists ra. auto.
  - intros Hc. apply eqb_spec.
    destruct (conn_to_S k p I ltac:(lia) _ _ Hc)
      as [E | (x & y & _ & _ & Ex & Ey & (r & P1 & P2))].
    + apply toN_inj in E. rewrite E in Pa. exact (path_det _ _ _ _ Pa Pb).
    + apply toN_inj in Ex. apply toN_inj in Ey. subst x y.
      rewrite (path_det _ _ _ _ Pa P1). exact (path_det _ _ _ _ P2 Pb).
Qed.

Lemma query_inv : forall k p, Inv k p -> ((φ k) < (φ q))%Z -> xu.[k] = false ->
  Inv (k + 1) p.
Proof.
  intros k p (L & B & C1 & C2) Hk U.
  pose proof q_bound. pose proof (to_Z_bounded k).
  assert (E1 : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
  split; [exact L|]. split; [exact B|]. split.
  - intros m Hm Hum. destruct (Z.eq_dec (φ m) (φ k)) as [E | E].
    + assert (m = k) by (apply to_Z_inj; exact E). subst m. congruence.
    + apply C1; [lia | exact Hum].
  - intros x y Hx Hy S. rewrite (toN_succ k Hk).
    apply (conn_mono (toN k)); [apply C2; assumption | lia].
Qed.

Lemma union_inv_uv : forall k p ra rb u v, Inv k p -> wf_par p -> ((φ k) < (φ q))%Z ->
  xu.[k] = true -> path p (xa.[k]) ra -> path p (xb.[k]) rb -> ra <> rb ->
  ((u = ra /\ v = rb) \/ (u = rb /\ v = ra)) ->
  Inv (k + 1) p.[u <- v].
Proof.
  intros k p ra rb u v I W Hk U Pa Pb Nab Huv.
  pose proof I as (L & B & C1 & C2).
  pose proof q_bound. pose proof (to_Z_bounded k).
  assert (E1 : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
  pose proof (rangeA k Hk) as RA. pose proof (rangeB k Hk) as RB.
  pose proof (path_range p _ B _ _ Pa RA) as Rra.
  pose proof (path_range p _ B _ _ Pb RB) as Rrb.
  pose proof (path_fix p _ _ Pa) as Fa. pose proof (path_fix p _ _ Pb) as Fb.
  assert (Fu : p.[u] = u /\ p.[v] = v /\ u <> v /\ ((φ u) < (φ xn))%Z /\ ((φ v) < (φ xn))%Z)
    by (destruct Huv as [[-> ->] | [-> ->]]; repeat split; auto).
  destruct Fu as (Fu & Fv & Nuv & Ru & Rv).
  assert (Hl : (u <? PArray.length p) = true) by (rewrite ltb_spec, L; exact Ru).
  assert (Sab : sameroot p.[u <- v] (xa.[k]) (xb.[k])).
  { assert (Sr : sameroot p.[u <- v] ra rb).
    { destruct Huv as [[-> ->] | [-> ->]].
      - exact (link_sameroot2 p ra rb Fu Fv Nuv Hl).
      - apply sameroot_sym. exact (link_sameroot2 p rb ra Fu Fv Nuv Hl). }
    apply (sameroot_trans _ _ ra).
    - apply link_sameroot1; auto. apply sameroot_root. exact Pa.
    - apply (sameroot_trans _ _ rb); [exact Sr|].
      apply sameroot_sym. apply link_sameroot1; auto. apply sameroot_root. exact Pb. }
  assert (Cab : conn (toN (k + 1)) (toN (xa.[k])) (toN (xb.[k]))).
  { rewrite <- (getA k Hk), <- (getB k Hk). apply conn_union.
    - rewrite (toN_succ k Hk). lia.
    - unfold union_op. rewrite (getU k Hk). exact U. }
  assert (Hxy : forall x y, ((φ x) < (φ xn))%Z -> ((φ y) < (φ xn))%Z ->
            sameroot p x ra -> sameroot p y rb -> conn (toN (k + 1)) (toN x) (toN y)).
  { intros x y Hx Hy Sx Sy.
    apply (conn_trans _ _ _ _ _ (toN (xa.[k]))).
    - apply (conn_mono (toN k)); [| rewrite (toN_succ k Hk); lia].
      apply C2; auto. apply (sameroot_trans _ _ ra); [exact Sx|].
      apply sameroot_sym. apply sameroot_root. exact Pa.
    - apply (conn_trans _ _ _ _ _ (toN (xb.[k]))); [exact Cab|].
      apply (conn_mono (toN k)); [| rewrite (toN_succ k Hk); lia].
      apply C2; auto. apply (sameroot_trans _ _ rb).
      + apply sameroot_root. exact Pb.
      + apply sameroot_sym. exact Sy. }
  split; [rewrite alength_set; exact L|]. split.
  - intros y Hy. destruct (get_set_cases p u y v) as [[_ G] | G]; rewrite G;
      [exact Rv | apply B; exact Hy].
  - split.
    + intros m Hm Hum. destruct (Z.eq_dec (φ m) (φ k)) as [E | E].
      * assert (m = k) by (apply to_Z_inj; exact E). subst m. exact Sab.
      * apply link_sameroot1; auto. apply C1; [lia | exact Hum].
    + intros x y Hx Hy S.
      destruct (link_sameroot3 p u v W Fu Fv Nuv Hl x y S)
        as [S0 | [[S1 S2] | [S1 S2]]].
      * rewrite (toN_succ k Hk). apply (conn_mono (toN k)); [apply C2; auto | lia].
      * destruct Huv as [[-> ->] | [-> ->]].
        -- apply Hxy; auto.
        -- apply conn_sym. apply Hxy; auto.
      * destruct Huv as [[-> ->] | [-> ->]].
        -- apply conn_sym. apply Hxy; auto.
        -- apply Hxy; auto.
Qed.

Lemma union_inv : forall k p rk ra rb, Inv k p -> wf_par p -> ((φ k) < (φ q))%Z ->
  xu.[k] = true -> path p (xa.[k]) ra -> path p (xb.[k]) rb ->
  Inv (k + 1) (fst (link p rk ra rb)).
Proof.
  intros k p rk ra rb I W Hk U Pa Pb.
  destruct (link_cases p rk ra rb) as [[E ->] | [Ne [-> | ->]]].
  - subst rb. pose proof I as (L & B & C1 & C2).
    pose proof q_bound. pose proof (to_Z_bounded k).
    assert (E1 : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
    split; [exact L|]. split; [exact B|]. split.
    + intros m Hm Hum. destruct (Z.eq_dec (φ m) (φ k)) as [E | E].
      * assert (m = k) by (apply to_Z_inj; exact E). subst m. exists ra. auto.
      * apply C1; [lia | exact Hum].
    + intros x y Hx Hy S. rewrite (toN_succ k Hk).
      apply (conn_mono (toN k)); [apply C2; assumption | lia].
  - apply (union_inv_uv k p ra rb); auto.
  - apply (union_inv_uv k p ra rb); auto.
Qed.

Lemma scan_spec : forall z k p rk out W H,
  gap q k = z -> ((φ k) <= (φ q))%Z -> Inv k p -> OutInv k out ->
  OutInv q (scan xu xa xb q k p rk out W H).
Proof.
  intros z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k p rk out W H Hz Hk I O.
  rewrite scan_eq. destruct (bdec (k <? q)) as [Hkq | Hkq].
  - pose proof Hkq as Hkq'. rewrite ltb_spec in Hkq'.
    pose proof q_bound. pose proof (to_Z_bounded k).
    assert (E1 : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
    cbv zeta.
    destruct (find_spec p (xa.[k]) (W (xa.[k]))) as (Pa & Ca & La).
    set (fa := find p (xa.[k]) (W (xa.[k]))) in *.
    set (Wa := find_wf p (xa.[k]) (W (xa.[k])) W) in *.
    pose proof (inv_transfer k p (snd fa) W Ca La I) as I1.
    destruct (find_spec (snd fa) (xb.[k]) (Wa (xb.[k]))) as (Pb & Cb & Lb).
    set (fb := find (snd fa) (xb.[k]) (Wa (xb.[k]))) in *.
    set (Wb := find_wf (snd fa) (xb.[k]) (Wa (xb.[k])) Wa) in *.
    pose proof (inv_transfer k (snd fa) (snd fb) Wa Cb Lb I1) as I2.
    pose proof (compat_path _ _ Cb _ _ (compat_path _ _ Ca _ _ Pa)) as Pa2.
    pose proof (compat_path _ _ Cb _ _ Pb) as Pb2.
    destruct O as [Lo O].
    destruct (xu.[k]) eqn:U.
    + eapply IH; [ | reflexivity | lia | | ].
      * rewrite <- Hz. apply dec_step. exact Hkq.
      * apply union_inv; assumption.
      * split; [exact Lo|]. intros j Hj Uj.
        destruct (Z.eq_dec (φ j) (φ k)) as [E | E].
        -- assert (j = k) by (apply to_Z_inj; exact E). subst j. congruence.
        -- apply O; [lia | exact Uj].
    + eapply IH; [ | reflexivity | lia | | ].
      * rewrite <- Hz. apply dec_step. exact Hkq.
      * apply query_inv; assumption.
      * split; [rewrite blength_set; exact Lo|]. intros j Hj Uj.
        destruct (Z.eq_dec (φ j) (φ k)) as [E | E].
        -- assert (j = k) by (apply to_Z_inj; exact E). subst j.
           rewrite bget_set_same by (rewrite Lo; exact Hkq).
           exact (query_correct k (snd fb) (fst fa) (fst fb) I2 Wb Hkq' Pa2 Pb2).
        -- rewrite bget_set_other by (intro F; apply E; rewrite F; reflexivity).
           apply O; [lia | exact Uj].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hkq.
    assert (k = q) by (apply to_Z_inj; lia). subst k. exact O.
Qed.

Lemma init_inv : Inv 0 (init_par xn).
Proof.
  pose proof xn_bounds as Bn.
  assert (Lm : PArray.length (PArray.make xn 0) = xn).
  { rewrite alength_make.
    replace (xn <=? PArray.max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  destruct (init_spec xn ltac:(lia) _ 0 (PArray.make xn 0)
              (Zwf_well_founded 0 (gap xn 0)) eq_refl Lm
              ltac:(change (φ 0) with 0%Z; lia)
              ltac:(intros y Hy; change (φ 0) with 0%Z in Hy;
                    pose proof (to_Z_bounded y); lia))
    as [L P].
  unfold init_par. split; [exact L|]. split.
  - intros y Hy. rewrite (P y Hy). exact Hy.
  - split.
    + intros m Hm. change (φ 0) with 0%Z in Hm. pose proof (to_Z_bounded m). lia.
    + intros x y Hx Hy (r & P1 & P2).
      rewrite (path_of_root _ x r (P x Hx) P1) in P2.
      rewrite <- (path_of_root _ y x (P y Hy) P2). apply conn_refl.
Qed.

Lemma run_ops_main : exists out : list bool,
  repr (run_ops_impl xn xu xa xb) out /\ run_ops_spec n is_union elt_a elt_b out.
Proof.
  unfold run_ops_impl. cbv zeta.
  pose proof q_bound as Bq.
  assert (O0 : OutInv 0 (PArray.make q false)).
  { split.
    - rewrite blength_make.
      replace (q <=? PArray.max_length) with true; [reflexivity|].
      symmetry. rewrite leb_spec, max_length_val. lia.
    - intros j Hj. change (φ 0) with 0%Z in Hj. pose proof (to_Z_bounded j). lia. }
  pose proof (scan_spec _ 0 (init_par xn) (PArray.make xn 0) (PArray.make q false)
                (init_wf xn) (Zwf_well_founded 0 (gap q 0)) eq_refl
                ltac:(change (φ 0) with 0%Z; pose proof (to_Z_bounded q); lia)
                init_inv O0) as [Lr Or].
  set (r := scan xu xa xb q 0 (init_par xn) (PArray.make xn 0) (PArray.make q false)
                (init_wf xn) (Zwf_well_founded 0 (gap q 0))) in *.
  exists (map (fun i => r.[of_nat i]) (seq 0 (List.length is_union))).
  assert (Hnth : forall i, (i < List.length is_union)%nat ->
            nth_error (map (fun i => r.[of_nat i]) (seq 0 (List.length is_union))) i
            = Some (r.[of_nat i])).
  { intros i Hi. rewrite nth_error_map, nth_error_seq.
    destruct (Nat.ltb_spec i (List.length is_union)); [reflexivity | lia]. }
  split.
  - split.
    + rewrite length_map, length_seq.
      exact (eq_trans (eq_sym q_val) (f_equal to_Z (eq_sym Lr))).
    + intros i Hi. rewrite length_map, length_seq in Hi.
      exists (r.[of_nat i]). split; [exact (Hnth i Hi) | reflexivity].
  - split.
    + unfold len. rewrite length_map, length_seq. reflexivity.
    + intros k Hk Hq. unfold len in Hk.
      set (j := of_nat (N.to_nat k)).
      assert (Hj : (φ j) = Z.of_N k).
      { unfold j. rewrite of_Z_spec. rewrite N_nat_Z. apply Z.mod_small. pose proof q_val. lia. }
      assert (Hjq : ((φ j) < (φ q))%Z) by (rewrite q_val; lia).
      assert (Tj : toN j = k) by (unfold toN; rewrite Hj; lia).
      unfold answers_query, get_list_bool at 1.
      erewrite nth_error_nth; [| apply Hnth; lia].
      fold j. rewrite <- Tj.
      assert (Uj : xu.[j] = false) by (rewrite <- (getU j Hjq), Tj; exact Hq).
      exact (Or j Hjq Uj).
Qed.

End Correct.

Theorem run_ops_impl_correct :
  forall (n : N) (is_union : list bool) (elt_a elt_b : list N)
         (xn : uint) (xu : array bool) (xa xb : array uint),
  valid_input n is_union elt_a elt_b ->
  repr xn n -> repr xu is_union -> repr xa elt_a -> repr xb elt_b ->
  exists out : list bool,
    repr (run_ops_impl xn xu xa xb) out /\ run_ops_spec n is_union elt_a elt_b out.
Proof.
  intros n is_union elt_a elt_b xn xu xa xb Hv Hn Hu Ha Hb.
  exact (run_ops_main n is_union elt_a elt_b xn xu xa xb Hv Hn Hu Ha Hb).
Qed.

Definition run_ops_correct :
  forall (n : N) (is_union : list bool) (elt_a elt_b : list N)
         (xn : uint) (xu : array bool) (xa xb : array uint),
  valid_input n is_union elt_a elt_b ->
  repr xn n -> repr xu is_union -> repr xa elt_a -> repr xb elt_b ->
  exists out : list bool,
    repr (run_ops xn xu xa xb) out /\ run_ops_spec n is_union elt_a elt_b out
  := run_ops_impl_correct.
