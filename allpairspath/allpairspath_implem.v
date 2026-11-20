(* Implementation of allpairspath (../spec/allpairspath.spec): all-pairs
   shortest walks with negative cycles, by Johnson's algorithm.

   Code (section "The program").
   - The graph is read through a forward star built once from the edge
     arrays: hd.[a] = 1 + the last edge leaving a, nx.[k] = 1 + the previous
     edge leaving the source of k (0: none); two flat int arrays.
   - Reachability: one breadth-first search per source, into a flat n * n
     boolean matrix R.
   - Bellman-Ford #1 (n rounds from a virtual source, potentials start at
     0) over the edges inside a strongly connected component (R.[b*n+a] for
     an edge a -> b).  The sources of the edges that still relax are the
     "bad" vertices: each lies on a negative closed walk, and every negative
     closed walk passes through one.
   - Bellman-Ford #2 over the edges between good vertices: that graph has
     no negative closed walk, so the result p is a feasible potential.
   - Per source u: a breadth-first search from the bad vertices reachable
     from u marks the NegInfinity cells; Dijkstra from u with a binary heap
     (lazy deletion, keys d * 256 + v in one int array) over the good edges
     reweighted by p gives the finite distances D.[v] - p.[u] + p.[v]; a
     cell reachable by no walk (R.[u*n+v] false) is Impossible.
   No nat, no Z and no list in the code: every loop terminates on an erased
   Acc (Zwf 0) argument (counted loops through [for_loop], edge chains
   through [chain_fold], the heap sifts, the BFS queue and the Dijkstra loop
   bounded by m + 1 pops).  Every array is threaded linearly.

   Proof.  Walks of the spec are walks [pw Ge] over the machine edges with
   their vertex list; [shorten] (a walk either carries a negative closed
   walk or can be replaced by a no-repeat walk that costs no more) gives the
   Bellman-Ford optimality, the characterisation of the bad vertices
   ([bad_neg], [neg_has_bad]) and the bounds on every value; Dijkstra is
   proven with the invariant [dinv] (final vertices are exact, every
   tentative distance has a heap entry, the frontier edges are relaxed, a
   counter bounds the pops). *)

From Allpairspath.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import Bool ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Psatz.
From Stdlib Require Sint63.
From KattisLib Require Import Cost.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ------------------------------------------------------------------ *)
(* The termination device and the counted loop                         *)
(* ------------------------------------------------------------------ *)

Definition bdec (b : bool) : {b = true} + {b = false} :=
  match b as b0 return {b0 = true} + {b0 = false} with
  | true => left eq_refl
  | false => right eq_refl
  end.
Elpi complexity sumbool.
Elpi complexity bdec.
Elpi complexity andb.
Elpi complexity negb.
Elpi complexity Sint63.ltb.

Definition gap (m j : int) : Z := ((φ m) - (φ j))%Z.

Lemma dec_step : forall m i : int,
  (i <? m) = true -> Zwf 0 (gap m (i + 1)) (gap m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

Section ForLoop.
  Context {S : Type} (f : int -> S -> S).

  Fixpoint for_acc (hi i : int) (s : S) (H : Acc (Zwf 0) (gap hi i)) {struct H} : S :=
    match bdec (i <? hi) with
    | left Hi => for_acc hi (i + 1) (f i s) (Acc_inv H (dec_step hi i Hi))
    | right _ => s
    end.

  Lemma for_acc_eq : forall hi i s H,
    for_acc hi i s H =
    match bdec (i <? hi) with
    | left Hi => for_acc hi (i + 1) (f i s) (Acc_inv H (dec_step hi i Hi))
    | right _ => s
    end.
  Proof. intros. destruct H. reflexivity. Qed.

  Definition for_loop (lo hi : int) (s : S) : S :=
    for_acc hi lo s (Zwf_well_founded 0 (gap hi lo)).

  Lemma for_loop_inv : forall (Inv : Z -> S -> Prop) (lo hi : int) (s : S),
    ((φ lo) <= (φ hi))%Z -> Inv (φ lo) s ->
    (forall (i : int) (s : S), ((φ lo) <= (φ i) < (φ hi))%Z -> Inv (φ i) s ->
       Inv ((φ i) + 1)%Z (f i s)) ->
    Inv (φ hi) (for_loop lo hi s).
  Proof.
    intros Inv lo hi s0 Hlh H0 Hstep. unfold for_loop.
    assert (G : forall z i s H, gap hi i = z -> ((φ lo) <= (φ i) <= (φ hi))%Z ->
              Inv (φ i) s -> Inv (φ hi) (for_acc hi i s H)).
    { intro z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
      intros i s H Hz Hi Hinv. rewrite for_acc_eq.
      destruct (bdec (i <? hi)) as [Hc | Hc].
      - pose proof Hc as Hc'. rewrite ltb_spec in Hc'.
        assert (E : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
        eapply IH; [ rewrite <- Hz; apply dec_step; exact Hc | reflexivity | lia | ].
        rewrite E. apply Hstep; [lia | exact Hinv].
      - rewrite <- Bool.not_true_iff_false, ltb_spec in Hc.
        replace (φ hi) with (φ i) by lia. exact Hinv. }
    eapply G; [reflexivity | lia | exact H0].
  Qed.
End ForLoop.
Elpi complexity for_acc.
Arguments for_acc_cost : simpl never.
Elpi complexity for_loop.
Arguments for_loop_cost : simpl never.

(* ------------------------------------------------------------------ *)
(* Uint63 / Sint63 plumbing                                            *)
(* ------------------------------------------------------------------ *)

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma max_length_val : (φ PArray.max_length) = 4194303%Z.
Proof. reflexivity. Qed.

Lemma alen_bound : forall A (t : array A), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros A t. pose proof (leb_length A t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

Lemma alen_make : forall A (n : int) (b : A), ((φ n) <= 4194303)%Z ->
  PArray.length (PArray.make n b) = n.
Proof.
  intros A n b H. rewrite length_make.
  replace (n <=? max_length) with true; [reflexivity|].
  symmetry. rewrite leb_spec, max_length_val. exact H.
Qed.

Lemma of_Z_phi : forall z, (0 <= z < wB)%Z -> (φ (of_Z z)) = z.
Proof. intros z H. rewrite of_Z_spec. apply Z.mod_small. exact H. Qed.

Lemma phi_inj : forall a b : int, (φ a) = (φ b) -> a = b.
Proof. intros a b H. apply to_Z_inj. exact H. Qed.

(* the signed reading of small words *)
Lemma s_small : forall z : Z, (-4611686018427387904 <= z < 4611686018427387904)%Z ->
  Sint63.cmod z wB = z.
Proof. intros z H. apply Sint63.cmod_small. rewrite wB_val. lia. Qed.

Lemma s_add : forall a b : int,
  (-4611686018427387904 <= Sint63.to_Z a + Sint63.to_Z b < 4611686018427387904)%Z ->
  Sint63.to_Z (a + b) = (Sint63.to_Z a + Sint63.to_Z b)%Z.
Proof. intros a b H. rewrite Sint63.add_spec. apply s_small. exact H. Qed.

Lemma s_sub : forall a b : int,
  (-4611686018427387904 <= Sint63.to_Z a - Sint63.to_Z b < 4611686018427387904)%Z ->
  Sint63.to_Z (a - b) = (Sint63.to_Z a - Sint63.to_Z b)%Z.
Proof. intros a b H. rewrite Sint63.sub_spec. apply s_small. exact H. Qed.

Lemma s_ltb : forall a b : int,
  Sint63.ltb a b = true <-> (Sint63.to_Z a < Sint63.to_Z b)%Z.
Proof. intros a b. rewrite Sint63.ltb_spec. rewrite Z.compare_lt_iff. tauto. Qed.

Lemma s_bounded : forall a : int,
  (-4611686018427387904 <= Sint63.to_Z a < 4611686018427387904)%Z.
Proof. intros a. pose proof (Sint63.to_Z_bounded a). cbn in H. lia. Qed.

(* a small non-negative word reads the same both ways *)
Lemma s_of_u : forall a : int, ((φ a) < 4611686018427387904)%Z -> Sint63.to_Z a = (φ a).
Proof.
  intros a H. rewrite Sint63.to_Z_cmodwB. apply s_small.
  pose proof (to_Z_bounded a). lia.
Qed.

Lemma u_of_s : forall a : int, (0 <= Sint63.to_Z a)%Z -> (φ a) = Sint63.to_Z a.
Proof.
  intros a H. rewrite <- (Sint63.to_Z_mod_Uint63to_Z a). apply Z.mod_small.
  pose proof (s_bounded a). rewrite wB_val. lia.
Qed.

(* the primitive-array lemmas, restated at the universe of our own arrays
   (rewrite does not match a universe instance other than the one of the
   lemma) *)
Lemma alen_set_i : forall (t : array int) (i : int) (b : int),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set int t i b). Qed.
Lemma aget_set_same_i : forall (t : array int) (i : int) (b : int),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same int t i b H). Qed.
Lemma aget_set_other_i : forall (t : array int) (i j : int) (b : int),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other int t i j b H). Qed.
Lemma aget_make_i : forall (n i : int) (b : int), (PArray.make n b).[i] = b.
Proof. intros n i b. exact (get_make int b n i). Qed.
Lemma alen_make_i : forall (n : int) (b : int), ((φ n) <= 4194303)%Z ->
  PArray.length (PArray.make n b) = n.
Proof. intros n b H. exact (alen_make int n b H). Qed.
Lemma alen_bound_i : forall (t : array int), ((φ (PArray.length t)) <= 4194303)%Z.
Proof. intros t. exact (alen_bound int t). Qed.
Lemma alen_set_b : forall (t : array bool) (i : int) (b : bool),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set bool t i b). Qed.
Lemma aget_set_same_b : forall (t : array bool) (i : int) (b : bool),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same bool t i b H). Qed.
Lemma aget_set_other_b : forall (t : array bool) (i j : int) (b : bool),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other bool t i j b H). Qed.
Lemma aget_make_b : forall (n i : int) (b : bool), (PArray.make n b).[i] = b.
Proof. intros n i b. exact (get_make bool b n i). Qed.
Lemma alen_make_b : forall (n : int) (b : bool), ((φ n) <= 4194303)%Z ->
  PArray.length (PArray.make n b) = n.
Proof. intros n b H. exact (alen_make bool n b H). Qed.
Lemma alen_bound_b : forall (t : array bool), ((φ (PArray.length t)) <= 4194303)%Z.
Proof. intros t. exact (alen_bound bool t). Qed.

(* ====================================================================== *)
(* Walks                                                                  *)
(* ====================================================================== *)
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* Walks over an edge relation, with their vertex list (last first)    *)
(* ------------------------------------------------------------------ *)

Section Walks.
  Variable E : Z -> Z -> Z -> Prop.

  Inductive pw (x : Z) : Z -> Z -> list Z -> Prop :=
  | pw_nil : pw x x 0 [x]
  | pw_cons : forall v v' w c L, pw x v c L -> E v v' w -> pw x v' (c + w) (v' :: L).

  Definition R (a b : Z) : Prop := exists c L, pw a b c L.

  Lemma pw_head : forall x y c L, pw x y c L -> exists L', L = y :: L'.
  Proof. intros x y c L H. destruct H; eexists; reflexivity. Qed.

  Lemma pw_app : forall y z c2 L2, pw y z c2 L2 ->
    forall x c1 L1, pw x y c1 L1 -> exists L, pw x z (c1 + c2) L.
  Proof.
    intros y z c2 L2 H. induction H as [| v v' w c L H IH He]; intros x c1 L1 H1.
    - exists L1. rewrite Z.add_0_r. exact H1.
    - destruct (IH x c1 L1 H1) as [L0 H0]. exists (v' :: L0).
      rewrite Z.add_assoc. econstructor; eauto.
  Qed.

  Lemma R_refl : forall x, R x x.
  Proof. intros x. exists 0, [x]. constructor. Qed.

  Lemma R_trans : forall x y z, R x y -> R y z -> R x z.
  Proof.
    intros x y z (c1 & L1 & H1) (c2 & L2 & H2).
    destruct (pw_app y z c2 L2 H2 x c1 L1 H1) as [L H]. exists (c1 + c2), L. exact H.
  Qed.

  Lemma R_edge : forall a b w, E a b w -> R a b.
  Proof. intros a b w H. exists (0 + w), [b; a]. econstructor; [constructor | exact H]. Qed.

  Lemma pw_iter : forall z c L, pw z z c L -> forall k : nat,
    exists L', pw z z (Z.of_nat k * c) L'.
  Proof.
    intros z c L H k. induction k as [| k IH].
    - exists [z]. constructor.
    - destruct IH as [L' H']. destruct (pw_app z z c L H z _ L' H') as [L0 H0].
      exists L0. replace (Z.of_nat (S k) * c) with (Z.of_nat k * c + c) by lia. exact H0.
  Qed.

  Lemma pw_split : forall x y c L, pw x y c L -> forall z, In z L ->
    exists c1 L1 c2 L2 P, pw x z c1 L1 /\ pw z y c2 L2 /\ c = c1 + c2 /\ L = P ++ L1.
  Proof.
    intros x y c L H. induction H as [| v v' w c L H IH He]; intros z Hz.
    - destruct Hz as [<- | []]. exists 0, [x], 0, [x], []. repeat split; constructor.
    - destruct (Z.eq_dec z v') as [<- | Hne].
      + exists (c + w), (z :: L), 0, [z], []. repeat split; try constructor.
        * econstructor; eauto.
        * lia.
      + destruct Hz as [Hz | Hz]; [congruence|].
        destruct (IH z Hz) as (c1 & L1 & c2 & L2 & P & H1 & H2 & Hc & HL).
        exists c1, L1, (c2 + w), (v' :: L2), (v' :: P). repeat split.
        * exact H1.
        * econstructor; eauto.
        * lia.
        * rewrite HL. reflexivity.
  Qed.

  Lemma pw_in_R : forall x y c L z, pw x y c L -> In z L -> R x z /\ R z y.
  Proof.
    intros x y c L z H Hz.
    destruct (pw_split x y c L H z Hz) as (c1 & L1 & c2 & L2 & P & H1 & H2 & _ & _).
    split; eexists; eexists; eassumption.
  Qed.

  (* Either a negative closed walk sits on the walk, or a walk with no
     repeated vertex costs at most as much. *)
  Lemma shorten : forall x y c L, pw x y c L ->
    (exists z, R x z /\ R z y /\ exists c1 L1, pw z z c1 L1 /\ c1 < 0) \/
    (exists c' L', pw x y c' L' /\ c' <= c /\ NoDup L').
  Proof.
    intros x y c L H. induction H as [| v v' w c L H IH He].
    - right. exists 0, [x]. repeat split; [constructor | lia | repeat constructor; simpl; tauto].
    - destruct IH as [(z & Hxz & Hzv & Hneg) | (c' & L' & H' & Hc' & Hnd)].
      + left. exists z. repeat split; [exact Hxz | | exact Hneg].
        apply (R_trans z v v'); [exact Hzv | eapply R_edge; eauto].
      + destruct (in_dec Z.eq_dec v' L') as [Hin | Hnin].
        * destruct (pw_split x v c' L' H' v' Hin) as (c1 & L1 & c2 & L2 & P & H1 & H2 & Hc & HL).
          destruct (Z_lt_le_dec (c2 + w) 0) as [Hlt | Hge].
          -- left. exists v'. repeat split.
             ++ exists c1, L1. exact H1.
             ++ apply R_refl.
             ++ exists (c2 + w), (v' :: L2). split; [econstructor; eauto | exact Hlt].
          -- right. exists c1, L1. repeat split; [exact H1 | lia |].
             rewrite HL in Hnd. apply NoDup_app_remove_l in Hnd. exact Hnd.
        * right. exists (c' + w), (v' :: L'). repeat split.
          -- econstructor; eauto.
          -- lia.
          -- constructor; assumption.
  Qed.

  Lemma pw_vertices : forall n, (forall a b w, E a b w -> 0 <= a < n /\ 0 <= b < n) ->
    forall x y c L, pw x y c L -> 0 <= x < n -> forall z, In z L -> 0 <= z < n.
  Proof.
    intros n HE x y c L H Hx. induction H as [| v v' w c L H IH He]; intros z Hz.
    - destruct Hz as [<- | []]. exact Hx.
    - destruct Hz as [Hz | Hz]; [subst z; apply (HE v v' w He) | apply IH; exact Hz].
  Qed.

  Lemma pw_start : forall n, (forall a b w, E a b w -> 0 <= a < n /\ 0 <= b < n) ->
    forall x y c L, pw x y c L -> 0 <= y < n -> 0 <= x < n.
  Proof.
    intros n HE x y c L H Hy. induction H as [| v v' w c L H IH He]; [exact Hy|].
    apply IH. apply (HE v v' w He).
  Qed.

  Lemma pw_cost : forall lo hi, (forall a b w, E a b w -> lo <= w <= hi) ->
    forall x y c L, pw x y c L ->
    lo * (Z.of_nat (List.length L) - 1) <= c <= hi * (Z.of_nat (List.length L) - 1).
  Proof.
    intros lo hi HE x y c L H. induction H as [| v v' w c L H IH He]; [simpl; lia|].
    pose proof (HE _ _ _ He). change (List.length (v' :: L)) with (S (List.length L)).
    replace (lo * (Z.of_nat (S (List.length L)) - 1)) with (lo * (Z.of_nat (List.length L) - 1) + lo) by lia.
    replace (hi * (Z.of_nat (S (List.length L)) - 1)) with (hi * (Z.of_nat (List.length L) - 1) + hi) by lia.
    generalize dependent (lo * (Z.of_nat (List.length L) - 1)).
    generalize dependent (hi * (Z.of_nat (List.length L) - 1)). intros. lia.
  Qed.

  Lemma pw_len_pos : forall x y c L, pw x y c L -> (1 <= List.length L)%nat.
  Proof. intros x y c L H. destruct H; simpl; lia. Qed.
End Walks.

Lemma nodup_len : forall n (L : list Z), NoDup L -> (forall z, In z L -> 0 <= z < n) ->
  Z.of_nat (List.length L) <= Z.max 0 n.
Proof.
  intros n L Hnd Hb.
  assert (Hi : incl L (map Z.of_nat (seq 0 (Z.to_nat n)))).
  { intros z Hz. apply in_map_iff. exists (Z.to_nat z). split; [|apply in_seq];
      pose proof (Hb z Hz); lia. }
  pose proof (NoDup_incl_length Hnd Hi) as H. rewrite length_map, length_seq in H. lia.
Qed.

Lemma pw_mono : forall (E E' : Z -> Z -> Z -> Prop),
  (forall a b w, E a b w -> E' a b w) ->
  forall x y c L, pw E x y c L -> pw E' x y c L.
Proof.
  intros E E' HE x y c L H. induction H; econstructor; eauto.
Qed.

Lemma pw_restrict : forall (E E' : Z -> Z -> Z -> Prop) x y c L,
  pw E x y c L ->
  (forall a b w, E a b w -> In a L -> In b L -> E' a b w) ->
  pw E' x y c L.
Proof.
  intros E E' x y c L H. induction H as [| v v' w c L H IH He]; intros HE.
  - constructor.
  - econstructor.
    + apply IH. intros a b w' Hab Ha Hb. apply HE; [exact Hab | right; exact Ha | right; exact Hb].
    + apply HE; [exact He | | left; reflexivity].
      right. destruct (pw_head E x v c L H) as [L' ->]. left. reflexivity.
Qed.

(* ====================================================================== *)
(* The binary heap                                                        *)
(* ====================================================================== *)
Open Scope uint63_scope.
Open Scope array_scope.
Open Scope bool_scope.

(* ------------------------------------------------------------------ *)
(* Array cells read as Z, at Z indices                                 *)
(* ------------------------------------------------------------------ *)

Definition at_ (t : array int) (z : Z) : Z := (φ (t.[of_Z z])).

Lemma of_Z_eq : forall (z : Z) (k : int), (0 <= z < wB)%Z -> (of_Z z = k <-> z = (φ k)).
Proof.
  intros z k Hz. split; intros H.
  - subst k. rewrite of_Z_phi by exact Hz. reflexivity.
  - subst z. apply of_to_Z.
Qed.

Lemma at_set : forall (t : array int) (k x : int) (z : Z),
  ((φ k) < (φ (PArray.length t)))%Z -> (0 <= z < wB)%Z ->
  at_ (t.[k <- x]) z = if Z.eqb z (φ k) then (φ x) else at_ t z.
Proof.
  intros t k x z Hk Hz. unfold at_.
  destruct (Z.eqb_spec z (φ k)) as [E | E].
  - replace (of_Z z) with k by (symmetry; apply of_Z_eq; auto).
    rewrite aget_set_same_i; [reflexivity|]. rewrite ltb_spec. exact Hk.
  - rewrite aget_set_other_i; [reflexivity|]. intro F. apply E. apply of_Z_eq; auto.
Qed.

Lemma at_phi : forall (t : array int) (k : int), at_ t (φ k) = (φ (t.[k])).
Proof. intros t k. unfold at_. rewrite of_to_Z. reflexivity. Qed.

Definition swap (t : array int) (i j : int) : array int :=
  let a := t.[i] in
  let b := t.[j] in
  t.[i <- b].[j <- a].
Elpi complexity swap.
Arguments swap_cost : simpl never.

Lemma swap_length : forall t i j, PArray.length (swap t i j) = PArray.length t.
Proof. intros. unfold swap. rewrite !alen_set_i. reflexivity. Qed.

Lemma at_swap : forall (t : array int) (i j : int) (z : Z),
  ((φ i) < (φ (PArray.length t)))%Z -> ((φ j) < (φ (PArray.length t)))%Z -> (0 <= z < wB)%Z ->
  at_ (swap t i j) z =
  if Z.eqb z (φ j) then at_ t (φ i) else if Z.eqb z (φ i) then at_ t (φ j) else at_ t z.
Proof.
  intros t i j z Hi Hj Hz. unfold swap.
  rewrite at_set by (try rewrite alen_set_i; auto).
  rewrite at_set by auto. rewrite !at_phi. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Binary min-heap on the cells [0, s) of an int array                 *)
(* ------------------------------------------------------------------ *)

Definition par (j : Z) : Z := ((j - 1) / 2)%Z.

Definition heap_ok (t : array int) (s : Z) : Prop :=
  forall j, (0 < j < s)%Z -> (at_ t (par j) <= at_ t j)%Z.

Definition ok_down (t : array int) (s i : Z) : Prop :=
  (forall j, (0 < j < s)%Z -> par j <> i -> (at_ t (par j) <= at_ t j)%Z) /\
  (forall j, (0 < j < s)%Z -> par j = i -> (0 < i)%Z -> (at_ t (par i) <= at_ t j)%Z).

Definition ok_up (t : array int) (s i : Z) : Prop :=
  (forall j, (0 < j < s)%Z -> j <> i -> (at_ t (par j) <= at_ t j)%Z) /\
  ((0 < i)%Z -> forall j, (0 < j < s)%Z -> par j = i -> (at_ t (par i) <= at_ t j)%Z).

Definition sameset (t t' : array int) (s : Z) : Prop :=
  (forall j, (0 <= j < s)%Z -> exists j', (0 <= j' < s)%Z /\ at_ t' j' = at_ t j) /\
  (forall j', (0 <= j' < s)%Z -> exists j, (0 <= j < s)%Z /\ at_ t' j' = at_ t j).

Lemma sameset_refl : forall t s, sameset t t s.
Proof. intros t s. split; intros j Hj; exists j; auto. Qed.

Lemma sameset_trans : forall t1 t2 t3 s, sameset t1 t2 s -> sameset t2 t3 s -> sameset t1 t3 s.
Proof.
  intros t1 t2 t3 s [A1 B1] [A2 B2]. split.
  - intros j Hj. destruct (A1 j Hj) as (j1 & Hj1 & E1). destruct (A2 j1 Hj1) as (j2 & Hj2 & E2).
    exists j2. split; [exact Hj2 | congruence].
  - intros j Hj. destruct (B2 j Hj) as (j1 & Hj1 & E1). destruct (B1 j1 Hj1) as (j2 & Hj2 & E2).
    exists j2. split; [exact Hj2 | congruence].
Qed.

Lemma sameset_swap : forall t (i j : int) s,
  ((φ i) < s)%Z -> ((φ j) < s)%Z -> (s <= (φ (PArray.length t)))%Z -> sameset t (swap t i j) s.
Proof.
  intros t i j s Hi Hj Hs. pose proof (to_Z_bounded i). pose proof (to_Z_bounded j).
  assert (Hw : (s < wB)%Z) by (pose proof (alen_bound_i t); rewrite wB_val; lia).
  split.
  - intros k Hk.
    destruct (Z.eq_dec k (φ i)) as [Ei | Ei]; [| destruct (Z.eq_dec k (φ j)) as [Ej | Ej]].
    + exists (φ j). split; [lia|]. rewrite at_swap by lia. rewrite Z.eqb_refl. congruence.
    + exists (φ i). split; [lia|]. rewrite at_swap by lia.
      destruct (Z.eqb_spec (φ i) (φ j)); [congruence|]. rewrite Z.eqb_refl. congruence.
    + exists k. split; [lia|]. rewrite at_swap by lia.
      destruct (Z.eqb_spec k (φ j)); [congruence|]. destruct (Z.eqb_spec k (φ i)); [congruence|].
      reflexivity.
  - intros k Hk. rewrite at_swap by lia.
    destruct (Z.eqb_spec k (φ j)); [exists (φ i); split; [lia | reflexivity]|].
    destruct (Z.eqb_spec k (φ i)); [exists (φ j); split; [lia | reflexivity]|].
    exists k. split; [lia | reflexivity].
Qed.

Lemma heap_min : forall t s, heap_ok t s -> forall j, (0 <= j < s)%Z -> (at_ t 0 <= at_ t j)%Z.
Proof.
  intros t s Hh j. induction j as [j IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros Hj. destruct (Z.eq_dec j 0) as [-> | Hne]; [lia|].
  assert (Hp : (0 <= par j < j)%Z) by (unfold par; Z.to_euclidean_division_equations; lia).
  specialize (IH (par j) ltac:(unfold Zwf; lia) ltac:(lia)).
  specialize (Hh j ltac:(lia)). lia.
Qed.

(* sift up *)
Lemma up_dec : forall i : int, (0 <? i) = true -> Zwf 0 (φ ((i - 1) / 2)) (φ i).
Proof. intros i H. rewrite ltb_spec in H. change (φ 0) with 0%Z in H. unfold Zwf. sia. Qed.

Fixpoint sift_up (t : array int) (i : int) (H : Acc (Zwf 0) (φ i)) {struct H} : array int :=
  match bdec (0 <? i) with
  | left Hi =>
      let p := (i - 1) / 2 in
      if t.[i] <? t.[p] then sift_up (swap t i p) p (Acc_inv H (up_dec i Hi)) else t
  | right _ => t
  end.
Elpi complexity sift_up.
Arguments sift_up_cost : simpl never.

Lemma sift_up_eq : forall t i H, sift_up t i H =
  match bdec (0 <? i) with
  | left Hi =>
      let p := (i - 1) / 2 in
      if t.[i] <? t.[p] then sift_up (swap t i p) p (Acc_inv H (up_dec i Hi)) else t
  | right _ => t
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma par_child : forall i j, (0 < j)%Z -> par j = i -> (j = 2 * i + 1 \/ j = 2 * i + 2)%Z.
Proof. intros i j Hj H. unfold par in H. Z.to_euclidean_division_equations; lia. Qed.

Lemma sift_up_spec : forall z t (i : int) H s,
  (φ i) = z -> ((φ i) < s)%Z -> (s <= (φ (PArray.length t)))%Z -> ok_up t s (φ i) ->
  let r := sift_up t i H in
  heap_ok r s /\ sameset t r s /\ PArray.length r = PArray.length t.
Proof.
  intro z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros t i H s Hz Hi Hs [U1 U2]. cbv zeta. rewrite sift_up_eq.
  assert (Hw : (s < wB)%Z) by (pose proof (alen_bound_i t); rewrite wB_val; lia).
  pose proof (to_Z_bounded i) as Bi.
  destruct (bdec (0 <? i)) as [Hi0 | Hi0].
  - cbv zeta. pose proof Hi0 as Hi0'. rewrite ltb_spec in Hi0'. change (φ 0) with 0%Z in Hi0'.
    assert (Ep : (φ ((i - 1) / 2)) = par (φ i)) by (unfold par; sia).
    set (p := (i - 1) / 2) in *.
    assert (Hp : (0 <= par (φ i) < (φ i))%Z) by (unfold par; Z.to_euclidean_division_equations; lia).
    destruct ((φ (t.[i])) <? (φ (t.[p])))%Z eqn:Ec.
    + replace (t.[i] <? t.[p]) with true by (symmetry; rewrite ltb_spec; lia).
      rewrite Z.ltb_lt in Ec.
      assert (Hl : PArray.length (swap t i p) = PArray.length t) by apply swap_length.
      assert (AS : forall k, (0 <= k < s)%Z -> at_ (swap t i p) k =
          if Z.eqb k (φ p) then at_ t (φ i) else if Z.eqb k (φ i) then at_ t (φ p) else at_ t k)
        by (intros k Hk; apply at_swap; lia).
      rewrite !at_phi in AS.
      destruct (IH (φ p) ltac:(unfold Zwf; lia) (swap t i p) p (Acc_inv H (up_dec i Hi0)) s
                   eq_refl ltac:(lia) ltac:(rewrite Hl; lia)) as (R1 & R2 & R3).
      * split.
        -- intros j Hj Hjp. assert (Hpj : (0 <= par j < j)%Z) by (unfold par; Z.to_euclidean_division_equations; lia).
           rewrite (AS j) by lia. rewrite (AS (par j)) by lia.
           destruct (Z.eqb_spec j (φ p)); [congruence|].
           destruct (Z.eqb_spec j (φ i)) as [Eji | Eji].
           ++ (* j = i: parent is p *)
              rewrite Eji, <- Ep, Z.eqb_refl. lia.
           ++ destruct (Z.eqb_spec (par j) (φ p)) as [Ejp | Ejp].
              ** (* sibling of i *)
                 pose proof (U1 j Hj Eji) as Hs1. rewrite Ejp in Hs1. rewrite at_phi in Hs1. lia.
              ** destruct (Z.eqb_spec (par j) (φ i)) as [Eji2 | Eji2].
                 --- (* child of i *)
                     assert (Hpos : (0 < (φ i))%Z) by lia.
                     pose proof (U2 Hpos j Hj Eji2) as Hc. rewrite <- Ep, at_phi in Hc. exact Hc.
                 --- apply U1; auto.
        -- intros Hp0 j Hj Hjp.
           assert (Hpj : (0 <= par j < j)%Z) by (unfold par; Z.to_euclidean_division_equations; lia).
           assert (Hpp : (0 <= par (φ p) < (φ p))%Z) by (unfold par; Z.to_euclidean_division_equations; lia).
           rewrite (AS j) by lia. rewrite (AS (par (φ p))) by lia.
           destruct (Z.eqb_spec (par (φ p)) (φ p)); [lia|].
           destruct (Z.eqb_spec (par (φ p)) (φ i)); [lia|].
           pose proof (U1 (φ p) ltac:(lia) ltac:(lia)) as Hpp'. rewrite at_phi in Hpp'.
           destruct (Z.eqb_spec j (φ p)); [lia|].
           destruct (Z.eqb_spec j (φ i)) as [Eji | Eji]; [lia|].
           pose proof (U1 j Hj Eji) as Hsj. rewrite Hjp in Hsj. rewrite at_phi in Hsj. lia.
      * split; [exact R1 | split; [apply (sameset_trans _ (swap t i p)); [apply sameset_swap; lia | exact R2] |
          exact (eq_trans R3 Hl)]].
    + replace (t.[i] <? t.[p]) with false by (symmetry; rewrite Z.ltb_ge in Ec;
        rewrite <- Bool.not_true_iff_false, ltb_spec; lia).
      split; [| split; [apply sameset_refl | reflexivity]].
      intros j Hj. destruct (Z.eq_dec j (φ i)) as [-> | Hne]; [| apply U1; auto].
      rewrite <- Ep, !at_phi. rewrite Z.ltb_ge in Ec. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hi0. change (φ 0) with 0%Z in Hi0.
    split; [| split; [apply sameset_refl | reflexivity]].
    intros j Hj. apply U1; lia.
Qed.

(* sift down *)
Lemma down_dec : forall s i c : int, ((i <? c) && (c <? s)) = true -> Zwf 0 (gap s c) (gap s i).
Proof.
  intros s i c H. apply andb_prop in H. destruct H as [H1 H2].
  rewrite ltb_spec in H1, H2. unfold Zwf, gap. pose proof (to_Z_bounded i). lia.
Qed.

Fixpoint sift_down (t : array int) (s i : int) (H : Acc (Zwf 0) (gap s i)) {struct H} : array int :=
  let l := 2 * i + 1 in
  if l <? s then
    let r := l + 1 in
    let c := if (r <? s) && (t.[r] <? t.[l]) then r else l in
    match bdec ((i <? c) && (c <? s)) with
    | left Hc =>
        if t.[c] <? t.[i] then sift_down (swap t i c) s c (Acc_inv H (down_dec s i c Hc)) else t
    | right _ => t
    end
  else t.
Elpi complexity sift_down.
Arguments sift_down_cost : simpl never.

Lemma sift_down_eq : forall t s i H, sift_down t s i H =
  let l := 2 * i + 1 in
  if l <? s then
    let r := l + 1 in
    let c := if (r <? s) && (t.[r] <? t.[l]) then r else l in
    match bdec ((i <? c) && (c <? s)) with
    | left Hc =>
        if t.[c] <? t.[i] then sift_down (swap t i c) s c (Acc_inv H (down_dec s i c Hc)) else t
    | right _ => t
    end
  else t.
Proof. intros. destruct H. reflexivity. Qed.

Lemma sift_down_spec : forall z t (s i : int) H,
  gap s i = z -> ((φ i) <= (φ s))%Z -> ((φ s) <= (φ (PArray.length t)))%Z -> ok_down t (φ s) (φ i) ->
  let r := sift_down t s i H in
  heap_ok r (φ s) /\ sameset t r (φ s) /\ PArray.length r = PArray.length t.
Proof.
  intro z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros t s i H Hz Hi Hs [D1 D2]. cbv zeta. rewrite sift_down_eq. cbv zeta.
  pose proof (alen_bound_i t) as Bt.
  assert (Hw : ((φ s) < wB)%Z) by (rewrite wB_val; lia).
  pose proof (to_Z_bounded i) as Bi.
  assert (El : (φ (2 * i + 1)) = (2 * (φ i) + 1)%Z) by sia.
  assert (Er : (φ (2 * i + 1 + 1)) = (2 * (φ i) + 2)%Z) by sia.
  set (l := 2 * i + 1) in *. set (r := l + 1) in *.
  destruct (l <? s) eqn:Els.
  - rewrite ltb_spec in Els.
    set (c := if (r <? s) && (t.[r] <? t.[l]) then r else l).
    assert (Hc : ((φ c) = (φ l) \/ (φ c) = (φ r)) /\ ((φ c) < (φ s))%Z /\
                 (at_ t (φ c) <= at_ t (φ l))%Z /\
                 (((φ r) < (φ s))%Z -> (at_ t (φ c) <= at_ t (φ r))%Z)).
    { unfold c. rewrite !at_phi. destruct (r <? s) eqn:Ers; simpl.
      - rewrite ltb_spec in Ers. destruct (t.[r] <? t.[l]) eqn:Ec.
        + rewrite ltb_spec in Ec. lia.
        + rewrite <- Bool.not_true_iff_false, ltb_spec in Ec. lia.
      - rewrite <- Bool.not_true_iff_false, ltb_spec in Ers. lia. }
    destruct Hc as (Hc1 & Hc2 & Hc3 & Hc4).
    assert (Hpc : par (φ c) = (φ i)) by (unfold par; Z.to_euclidean_division_equations; lia).
    assert (G : ((i <? c) && (c <? s)) = true)
      by (apply andb_true_intro; split; rewrite ltb_spec; lia).
    destruct (bdec ((i <? c) && (c <? s))) as [Hg | Hg]; [| congruence].
    assert (Hlen : PArray.length (swap t i c) = PArray.length t) by apply swap_length.
    destruct (t.[c] <? t.[i]) eqn:Eci.
    + rewrite ltb_spec in Eci.
      assert (AS : forall k, (0 <= k < (φ s))%Z -> at_ (swap t i c) k =
          if Z.eqb k (φ c) then at_ t (φ i) else if Z.eqb k (φ i) then at_ t (φ c) else at_ t k)
        by (intros k Hk; apply at_swap; lia).
      rewrite !at_phi in AS, Hc3, Hc4.
      destruct (IH (gap s c) ltac:(rewrite <- Hz; apply down_dec; exact Hg)
                   (swap t i c) s c (Acc_inv H (down_dec s i c Hg))
                   eq_refl ltac:(lia) ltac:(rewrite Hlen; lia)) as (R1 & R2 & R3).
      * split.
        -- intros j Hj Hjc.
           assert (Hpj : (0 <= par j < j)%Z) by (unfold par; Z.to_euclidean_division_equations; lia).
           rewrite (AS j) by lia. rewrite (AS (par j)) by lia.
           destruct (Z.eqb_spec (par j) (φ c)); [congruence|].
           destruct (Z.eqb_spec j (φ c)) as [Ejc | Ejc].
           ++ rewrite Ejc, Hpc, Z.eqb_refl. lia.
           ++ destruct (Z.eqb_spec (par j) (φ i)) as [Eji | Eji].
              ** (* sibling of c *)
                 destruct (Z.eqb_spec j (φ i)); [lia|].
                 destruct (par_child (φ i) j ltac:(lia) Eji) as [Ej | Ej].
                 --- rewrite Ej, <- El, at_phi. lia.
                 --- rewrite Ej, <- Er, at_phi. specialize (Hc4 ltac:(lia)). lia.
              ** destruct (Z.eqb_spec j (φ i)) as [Eji2 | Eji2].
                 --- (* j = i, i > 0 *)
                     pose proof (D2 (φ c) ltac:(lia) Hpc ltac:(lia)) as Hd.
                     rewrite Eji2 in *. rewrite at_phi in Hd. lia.
                 --- apply D1; auto.
        -- intros j Hj Hjc Hc0.
           rewrite Hpc.
           assert (Hpj : (0 <= par j < j)%Z) by (unfold par; Z.to_euclidean_division_equations; lia).
           rewrite (AS j) by lia. rewrite (AS (φ i)) by lia.
           destruct (Z.eqb_spec (φ i) (φ c)); [lia|]. rewrite Z.eqb_refl.
           destruct (Z.eqb_spec j (φ c)); [lia|]. destruct (Z.eqb_spec j (φ i)); [lia|].
           pose proof (D1 j Hj ltac:(lia)) as Hd. rewrite Hjc, at_phi in Hd. exact Hd.
      * split; [exact R1 | split;
          [apply (sameset_trans _ (swap t i c)); [apply sameset_swap; lia | exact R2] |
           exact (eq_trans R3 Hlen)]].
    + rewrite <- Bool.not_true_iff_false, ltb_spec in Eci.
      split; [| split; [apply sameset_refl | reflexivity]].
      intros j Hj. destruct (Z.eq_dec (par j) (φ i)) as [Eji | Eji]; [| apply D1; auto].
      rewrite Eji. rewrite !at_phi in Hc3, Hc4. rewrite at_phi.
      destruct (par_child (φ i) j ltac:(lia) Eji) as [Ej | Ej].
      * rewrite Ej, <- El, at_phi. lia.
      * rewrite Ej, <- Er, at_phi. specialize (Hc4 ltac:(lia)). lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Els.
    split; [| split; [apply sameset_refl | reflexivity]].
    intros j Hj. apply D1; [exact Hj|]. intro E.
    destruct (par_child (φ i) j ltac:(lia) E); lia.
Qed.

(* push and pop *)
Definition hpush (t : array int) (s x : int) : array int :=
  sift_up t.[s <- x] s (Zwf_well_founded 0 (φ s)).
Elpi complexity hpush.
Arguments hpush_cost : simpl never.

Lemma hpush_spec : forall t s x,
  heap_ok t (φ s) -> ((φ s) < (φ (PArray.length t)))%Z ->
  let r := hpush t s x in
  heap_ok r ((φ s) + 1) /\ PArray.length r = PArray.length t /\
  (forall j, (0 <= j < (φ s))%Z -> exists j', (0 <= j' < (φ s) + 1)%Z /\ at_ r j' = at_ t j) /\
  (exists j', (0 <= j' < (φ s) + 1)%Z /\ at_ r j' = (φ x)) /\
  (forall j', (0 <= j' < (φ s) + 1)%Z ->
     at_ r j' = (φ x) \/ exists j, (0 <= j < (φ s))%Z /\ at_ r j' = at_ t j).
Proof.
  intros t s x Hh Hs. cbv zeta. unfold hpush.
  pose proof (alen_bound_i t) as Bt.
  assert (Hw : ((φ s) + 1 < wB)%Z) by (rewrite wB_val; lia).
  assert (A1 : forall k, (0 <= k < (φ s) + 1)%Z -> at_ t.[s <- x] k = if Z.eqb k (φ s) then (φ x) else at_ t k)
    by (intros k Hk; apply at_set; lia).
  destruct (sift_up_spec (φ s) t.[s <- x] s (Zwf_well_founded 0 (φ s)) ((φ s) + 1)
              eq_refl ltac:(lia) ltac:(rewrite alen_set_i; lia)) as (R1 & [S1 S2] & R3).
  { split.
    - intros j Hj Hjs. assert (Hpj : (0 <= par j < j)%Z) by (unfold par; Z.to_euclidean_division_equations; lia).
      rewrite !A1 by lia. destruct (Z.eqb_spec j (φ s)); [lia|].
      destruct (Z.eqb_spec (par j) (φ s)); [lia|]. apply Hh. lia.
    - intros Hs0 j Hj Hjp. unfold par in Hjp. Z.to_euclidean_division_equations; lia. }
  rewrite alen_set_i in R3.
  split; [exact R1 | split; [exact R3 | split; [| split]]].
  - intros j Hj. destruct (S1 j ltac:(lia)) as (j' & Hj' & E). exists j'. split; [exact Hj'|].
    rewrite E, A1 by lia. destruct (Z.eqb_spec j (φ s)); [lia | reflexivity].
  - destruct (S1 (φ s) ltac:(lia)) as (j' & Hj' & E). exists j'. split; [exact Hj'|].
    rewrite E, A1 by lia. rewrite Z.eqb_refl. reflexivity.
  - intros j' Hj'. destruct (S2 j' Hj') as (j & Hj & E). rewrite E, A1 by lia.
    destruct (Z.eqb_spec j (φ s)); [left; reflexivity | right; exists j; split; [lia | reflexivity]].
Qed.

Definition hpop (t : array int) (s : int) : int * array int :=
  let top := t.[0] in
  let s' := s - 1 in
  let last := t.[s'] in
  (top, sift_down t.[0 <- last] s' 0 (Zwf_well_founded 0 (gap s' 0))).
Elpi complexity hpop.
Arguments hpop_cost : simpl never.

Lemma hpop_spec : forall t s,
  heap_ok t (φ s) -> (0 < (φ s))%Z -> ((φ s) <= (φ (PArray.length t)))%Z ->
  let r := snd (hpop t s) in
  fst (hpop t s) = t.[0] /\
  (forall j, (0 <= j < (φ s))%Z -> ((φ (t.[0])) <= at_ t j)%Z) /\
  heap_ok r ((φ s) - 1) /\ PArray.length r = PArray.length t /\
  (forall j', (0 <= j' < (φ s) - 1)%Z -> exists j, (0 <= j < (φ s))%Z /\ at_ r j' = at_ t j) /\
  (forall j, (1 <= j < (φ s))%Z -> exists j', (0 <= j' < (φ s) - 1)%Z /\ at_ r j' = at_ t j).
Proof.
  intros t s Hh Hs0 Hs. cbv zeta. unfold hpop. simpl.
  pose proof (alen_bound_i t) as Bt.
  assert (Hw : ((φ s) < wB)%Z) by (rewrite wB_val; lia).
  assert (Es : (φ (s - 1)) = ((φ s) - 1)%Z) by sia.
  assert (A1 : forall k, (0 <= k < (φ s))%Z ->
     at_ t.[0 <- t.[s - 1]] k = if Z.eqb k 0 then at_ t ((φ s) - 1) else at_ t k).
  { intros k Hk. rewrite at_set by (change (φ 0) with 0%Z; lia). change (φ 0) with 0%Z.
    rewrite <- Es, at_phi. reflexivity. }
  destruct (sift_down_spec _ t.[0 <- t.[s - 1]] (s - 1) 0 (Zwf_well_founded 0 (gap (s - 1) 0))
              eq_refl ltac:(change (φ 0) with 0%Z; lia) ltac:(rewrite alen_set_i; lia))
    as (R1 & [S1 S2] & R3).
  { change (φ 0) with 0%Z. split; [| intros; lia].
    intros j Hj Hjp. assert (Hpj : (0 <= par j < j)%Z) by (unfold par; Z.to_euclidean_division_equations; lia).
    rewrite !A1 by lia. destruct (Z.eqb_spec j 0); [lia|].
    destruct (Z.eqb_spec (par j) 0); [lia|]. apply Hh. lia. }
  rewrite Es in R1, S1, S2. rewrite alen_set_i in R3.
  split; [reflexivity | split; [| split; [exact R1 | split; [exact R3 | split]]]].
  - intros j Hj. rewrite <- (at_phi t 0). change (φ 0) with 0%Z. apply (heap_min t (φ s)); auto.
  - intros j' Hj'. destruct (S2 j' Hj') as (j & Hj & E). rewrite E, A1 by lia.
    destruct (Z.eqb_spec j 0); [exists ((φ s) - 1)%Z; split; [lia | reflexivity] |
                                exists j; split; [lia | reflexivity]].
  - intros j Hj. destruct (Z.eq_dec j ((φ s) - 1)) as [Ej | Ej].
    + destruct (S1 0%Z ltac:(lia)) as (j' & Hj' & E). exists j'. split; [exact Hj'|].
      rewrite E, A1 by lia. rewrite Z.eqb_refl. congruence.
    + destruct (S1 j ltac:(lia)) as (j' & Hj' & E). exists j'. split; [exact Hj'|].
      rewrite E, A1 by lia. destruct (Z.eqb_spec j 0); [lia | reflexivity].
Qed.

(* ====================================================================== *)
(* The program (what gets extracted)                                      *)
(* ====================================================================== *)
Open Scope uint63_scope.
Open Scope array_scope.
Open Scope bool_scope.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* Forward star: hd.[a] = 1 + the last edge leaving a (0: none), and
   nx.[k] = 1 + the previous edge leaving the source of k (0: none). *)
Definition adj_step (us : array int) (k : int) (st : array int * array int)
    : array int * array int :=
  let (hd, nx) := st in
  let a := us.[k] in
  let old := hd.[a] in
  let nx' := nx.[k <- old] in
  let hd' := hd.[a <- k + 1] in
  (hd', nx').
Elpi complexity adj_step.
Arguments adj_step_cost : simpl never.

Definition build_adj (n m : int) (us : array int) : array int * array int :=
  for_loop (adj_step us) 0 m (PArray.make n 0, PArray.make m 0).
Elpi complexity build_adj.
Arguments build_adj_cost : simpl never.

(* Folding f over the chain of edges cur - 1, nx.[cur - 1] - 1, ... *)
Lemma chain_dec : forall c' cur : int, (c' <? cur) = true -> Zwf 0 (φ c') (φ cur).
Proof.
  intros c' cur H. rewrite ltb_spec in H. unfold Zwf. pose proof (to_Z_bounded c'). lia.
Qed.

Section Chain.
  Context {S : Type} (nx : array int) (f : int -> S -> S).

  Fixpoint chain_acc (cur : int) (s : S) (H : Acc (Zwf 0) (φ cur)) {struct H} : S :=
    match bdec (0 <? cur) with
    | left _ =>
        let e := cur - 1 in
        let s' := f e s in
        let c' := nx.[e] in
        match bdec (c' <? cur) with
        | left Hlt => chain_acc c' s' (Acc_inv H (chain_dec c' cur Hlt))
        | right _ => s'
        end
    | right _ => s
    end.

  Lemma chain_acc_eq : forall cur s H, chain_acc cur s H =
    match bdec (0 <? cur) with
    | left _ =>
        let e := cur - 1 in
        let s' := f e s in
        let c' := nx.[e] in
        match bdec (c' <? cur) with
        | left Hlt => chain_acc c' s' (Acc_inv H (chain_dec c' cur Hlt))
        | right _ => s'
        end
    | right _ => s
    end.
  Proof. intros. destruct H. reflexivity. Qed.

  Definition chain_fold (cur : int) (s : S) : S :=
    chain_acc cur s (Zwf_well_founded 0 (φ cur)).
End Chain.
Elpi complexity chain_acc.
Arguments chain_acc_cost : simpl never.
Elpi complexity chain_fold.
Arguments chain_fold_cost : simpl never.

(* Breadth-first closure of a set of seeds.  State: marks, queue, tail. *)
Definition bfs_visit (vs : array int) (e : int) (st : array bool * array int * int)
    : array bool * array int * int :=
  let '(mark, q, tl) := st in
  let b := vs.[e] in
  if mark.[b] then st else (mark.[b <- true], q.[tl <- b], tl + 1).
Elpi complexity bfs_visit.
Arguments bfs_visit_cost : simpl never.

Lemma bfs_dec : forall cap h tl : int, ((h <? tl) && (h <? cap)) = true ->
  Zwf 0 (gap cap (h + 1)) (gap cap h).
Proof. intros cap h tl H. apply andb_prop in H. apply dec_step. apply H. Qed.

Fixpoint bfs_acc (hd nx vs : array int) (cap h : int) (st : array bool * array int * int)
    (H : Acc (Zwf 0) (gap cap h)) {struct H} : array bool :=
  let '(mark, q, tl) := st in
  match bdec ((h <? tl) && (h <? cap)) with
  | left Hc =>
      let x := q.[h] in
      bfs_acc hd nx vs cap (h + 1) (chain_fold nx (bfs_visit vs) hd.[x] st)
        (Acc_inv H (bfs_dec cap h tl Hc))
  | right _ => mark
  end.
Elpi complexity bfs_acc.
Arguments bfs_acc_cost : simpl never.

Lemma bfs_acc_eq : forall hd nx vs cap h st H, bfs_acc hd nx vs cap h st H =
  let '(mark, q, tl) := st in
  match bdec ((h <? tl) && (h <? cap)) with
  | left Hc =>
      let x := q.[h] in
      bfs_acc hd nx vs cap (h + 1) (chain_fold nx (bfs_visit vs) hd.[x] st)
        (Acc_inv H (bfs_dec cap h tl Hc))
  | right _ => mark
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition seed_step (seed : array bool) (a : int) (st : array bool * array int * int)
    : array bool * array int * int :=
  let '(mark, q, tl) := st in
  if seed.[a] then (mark.[a <- true], q.[tl <- a], tl + 1) else st.
Elpi complexity seed_step.
Arguments seed_step_cost : simpl never.

Definition closure (n : int) (hd nx vs : array int) (seed : array bool) : array bool :=
  let st0 := for_loop (seed_step seed) 0 n (PArray.make n false, PArray.make n 0, 0) in
  bfs_acc hd nx vs n 0 st0 (Zwf_well_founded 0 (gap n 0)).
Elpi complexity closure.
Arguments closure_cost : simpl never.

(* The reachability matrix, flat: cell s * n + v. *)
Definition copy_step (n s : int) (row : array bool) (v : int) (r : array bool) : array bool :=
  r.[s * n + v <- row.[v]].
Elpi complexity copy_step.
Arguments copy_step_cost : simpl never.

Definition reach_row (n : int) (hd nx vs : array int) (s : int) (r : array bool) : array bool :=
  let row := closure n hd nx vs (PArray.make n false).[s <- true] in
  for_loop (copy_step n s row) 0 n r.
Elpi complexity reach_row.
Arguments reach_row_cost : simpl never.

Definition reach_matrix (n : int) (hd nx vs : array int) : array bool :=
  for_loop (reach_row n hd nx vs) 0 n (PArray.make (n * n) false).
Elpi complexity reach_matrix.
Arguments reach_matrix_cost : simpl never.

(* Bellman-Ford from a virtual source, over the edges k with keep k. *)
Definition bf_edge (us vs ws : array int) (keep : int -> bool) (k : int) (h : array int)
    : array int :=
  if keep k then
    let a := us.[k] in
    let b := vs.[k] in
    let nb := h.[a] + ws.[k] in
    if Sint63.ltb nb h.[b] then h.[b <- nb] else h
  else h.
Elpi complexity bf_edge.
Arguments bf_edge_cost : simpl never.

Definition bf_round (m : int) (us vs ws : array int) (keep : int -> bool) (r : int)
    (h : array int) : array int :=
  for_loop (bf_edge us vs ws keep) 0 m h.
Elpi complexity bf_round.
Arguments bf_round_cost : simpl never.

Definition bf (n m : int) (us vs ws : array int) (keep : int -> bool) : array int :=
  for_loop (bf_round m us vs ws keep) 0 n (PArray.make n 0).
Elpi complexity bf.
Arguments bf_cost : simpl never.

(* The sources of the edges inside a strongly connected component that
   still relax after Bellman-Ford over those edges. *)
Definition bad_step (n : int) (us vs ws : array int) (R : array bool) (h : array int)
    (k : int) (bad : array bool) : array bool :=
  let a := us.[k] in
  let b := vs.[k] in
  if R.[b * n + a] && Sint63.ltb (h.[a] + ws.[k]) h.[b] then bad.[a <- true] else bad.
Elpi complexity bad_step.
Arguments bad_step_cost : simpl never.

(* Dijkstra with a binary heap of keys d * 256 + v, on the edges between
   good vertices, reweighted by the potentials p. *)
Definition INF : int := 1073741824.
Elpi complexity INF.
Arguments INF_cost : simpl never.

Definition relax (vs ws : array int) (bad done : array bool) (p : array int) (v d : int)
    (e : int) (st : array int * array int * int) : array int * array int * int :=
  let '(D, hp, sz) := st in
  let b := vs.[e] in
  if negb bad.[b] && negb done.[b] then
    let nd := d + ws.[e] + p.[v] - p.[b] in
    if nd <? D.[b] then (D.[b <- nd], hpush hp sz (nd * 256 + b), sz + 1) else st
  else st.
Elpi complexity relax.
Arguments relax_cost : simpl never.

Lemma dij_dec : forall lim steps sz : int, ((0 <? sz) && (steps <? lim)) = true ->
  Zwf 0 (gap lim (steps + 1)) (gap lim steps).
Proof. intros lim steps sz H. apply andb_prop in H. apply dec_step. apply H. Qed.

Definition dij_body (hd nx vs ws : array int) (bad : array bool) (p : array int)
    (st : array int * array bool * array int * int) : array int * array bool * array int * int :=
  let '(D, done, hp, sz) := st in
  let (top, hp1) := hpop hp sz in
  let sz1 := sz - 1 in
  let v := top mod 256 in
  let d := top / 256 in
  if done.[v] then (D, done, hp1, sz1)
  else
    let done' := done.[v <- true] in
    let D' := D.[v <- d] in
    if bad.[v] then (D', done', hp1, sz1)
    else
      let '(D2, hp2, sz2) := chain_fold nx (relax vs ws bad done' p v d) hd.[v] (D', hp1, sz1) in
      (D2, done', hp2, sz2).
Elpi complexity dij_body.
Arguments dij_body_cost : simpl never.

Fixpoint dij_acc (hd nx vs ws : array int) (bad : array bool) (p : array int) (lim steps : int)
    (st : array int * array bool * array int * int) (H : Acc (Zwf 0) (gap lim steps)) {struct H}
    : array int :=
  let '(D, done, hp, sz) := st in
  match bdec ((0 <? sz) && (steps <? lim)) with
  | left Hc =>
      dij_acc hd nx vs ws bad p lim (steps + 1) (dij_body hd nx vs ws bad p st)
        (Acc_inv H (dij_dec lim steps sz Hc))
  | right _ => D
  end.
Elpi complexity dij_acc.
Arguments dij_acc_cost : simpl never.

Lemma dij_acc_eq : forall hd nx vs ws bad p lim steps st H,
  dij_acc hd nx vs ws bad p lim steps st H =
  let '(D, done, hp, sz) := st in
  match bdec ((0 <? sz) && (steps <? lim)) with
  | left Hc =>
      dij_acc hd nx vs ws bad p lim (steps + 1) (dij_body hd nx vs ws bad p st)
        (Acc_inv H (dij_dec lim steps sz Hc))
  | right _ => D
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition dijkstra (n m : int) (hd nx vs ws : array int) (bad : array bool) (p : array int)
    (u : int) : array int :=
  let D0 := (PArray.make n INF).[u <- 0] in
  let hp0 := (PArray.make (m + 1) 0).[0 <- u] in
  dij_acc hd nx vs ws bad p (m + 1) 0 (D0, PArray.make n false, hp0, 1)
    (Zwf_well_founded 0 (gap (m + 1) 0)).
Elpi complexity dijkstra.
Arguments dijkstra_cost : simpl never.

(* One row of the answer. *)
Definition cell (n : int) (R neg : array bool) (D p : array int) (u v : int) : answer int :=
  if neg.[v] then NegInfinity
  else if R.[u * n + v] then Distance (D.[v] - p.[u] + p.[v])
  else Impossible.
Elpi complexity cell.
Arguments cell_cost : simpl never.

Definition negseed_step (n : int) (R bad : array bool) (u a : int) (s : array bool)
    : array bool :=
  if bad.[a] && R.[u * n + a] then s.[a <- true] else s.
Elpi complexity negseed_step.
Arguments negseed_step_cost : simpl never.

Definition row_of (n m : int) (hd nx vs ws : array int) (R bad : array bool) (p : array int)
    (u : int) : array (answer int) :=
  let seed := for_loop (negseed_step n R bad u) 0 n (PArray.make n false) in
  let neg := closure n hd nx vs seed in
  let D := dijkstra n m hd nx vs ws bad p u in
  for_loop (fun v r => r.[v <- cell n R neg D p u v]) 0 n (PArray.make n Impossible).
Elpi complexity row_of.
Arguments row_of_cost : simpl never.

(* The rows of the answer, and the phases after the forward star, as two
   definitions of their own (cost proof: a single body made the cost
   translation too large for the kernel to re-check its reduction). *)
Definition apsp_rows (n m : int) (hd nx vs ws : array int) (R bad : array bool) (p : array int)
    : array (array (answer int)) :=
  for_loop (fun u res => res.[u <- row_of n m hd nx vs ws R bad p u]) 0 n
    (PArray.make n (PArray.make 0 Impossible)).
Elpi complexity apsp_rows.
Arguments apsp_rows_cost : simpl never.

Definition apsp_core (n m : int) (us vs ws hd nx : array int) : array (array (answer int)) :=
  let R := reach_matrix n hd nx vs in
  let h1 := bf n m us vs ws (fun k => R.[vs.[k] * n + us.[k]]) in
  let bad := for_loop (bad_step n us vs ws R h1) 0 m (PArray.make n false) in
  let p := bf n m us vs ws (fun k => negb bad.[us.[k]] && negb bad.[vs.[k]]) in
  apsp_rows n m hd nx vs ws R bad p.
Elpi complexity apsp_core.
Arguments apsp_core_cost : simpl never.

Definition allpairspath_impl (n : int) (us vs ws : array int) : array (array (answer int)) :=
  let m := PArray.length us in
  let (hd, nx) := build_adj n m us in
  apsp_core n m us vs ws hd nx.
Elpi complexity allpairspath_impl.
Arguments allpairspath_impl_cost : simpl never.

(* ====================================================================== *)
(* Correctness                                                            *)
(* ====================================================================== *)
Open Scope uint63_scope.
Open Scope array_scope.
Open Scope bool_scope.

Definition atb (t : array bool) (z : Z) : bool := t.[of_Z z].

Lemma atb_set : forall (t : array bool) (k : int) (x : bool) (z : Z),
  ((φ k) < (φ (PArray.length t)))%Z -> (0 <= z < wB)%Z ->
  atb (t.[k <- x]) z = if Z.eqb z (φ k) then x else atb t z.
Proof.
  intros t k x z Hk Hz. unfold atb.
  destruct (Z.eqb_spec z (φ k)) as [E | E].
  - replace (of_Z z) with k by (symmetry; apply of_Z_eq; auto).
    rewrite aget_set_same_b; [reflexivity|]. rewrite ltb_spec. exact Hk.
  - rewrite aget_set_other_b; [reflexivity|]. intro F. apply E. apply of_Z_eq; auto.
Qed.

Lemma atb_phi : forall (t : array bool) (k : int), atb t (φ k) = t.[k].
Proof. intros t k. unfold atb. rewrite of_to_Z. reflexivity. Qed.

Lemma atb_make : forall n b z, atb (PArray.make n b) z = b.
Proof. intros. unfold atb. apply aget_make_b. Qed.

Lemma at_make : forall n b z, at_ (PArray.make n b) z = (φ b).
Proof. intros. unfold at_. rewrite aget_make_i. reflexivity. Qed.

Lemma phi_add1 : forall k : int, ((φ k) < 4611686018427387904)%Z -> (φ (k + 1)) = ((φ k) + 1)%Z.
Proof. intros k H. sia. Qed.

Lemma alen_set_a : forall (t : array (answer int)) (i : int) (b : (answer int)),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set _ t i b). Qed.
Lemma aget_set_same_a : forall (t : array (answer int)) (i : int) (b : (answer int)),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same _ t i b H). Qed.
Lemma aget_set_other_a : forall (t : array (answer int)) (i j : int) (b : (answer int)),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other _ t i j b H). Qed.
Lemma alen_make_a : forall (n : int) (b : (answer int)), ((φ n) <= 4194303)%Z ->
  PArray.length (PArray.make n b) = n.
Proof. intros n b H. exact (alen_make _ n b H). Qed.
Lemma alen_set_r : forall (t : array (array (answer int))) (i : int) (b : (array (answer int))),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set _ t i b). Qed.
Lemma aget_set_same_r : forall (t : array (array (answer int))) (i : int) (b : (array (answer int))),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same _ t i b H). Qed.
Lemma aget_set_other_r : forall (t : array (array (answer int))) (i j : int) (b : (array (answer int))),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other _ t i j b H). Qed.
Lemma alen_make_r : forall (n : int) (b : (array (answer int))), ((φ n) <= 4194303)%Z ->
  PArray.length (PArray.make n b) = n.
Proof. intros n b H. exact (alen_make _ n b H). Qed.

Lemma inj_bound : forall (f : Z -> Z) (t N0 : Z), (0 <= t)%Z ->
  (forall j, (0 <= j < t)%Z -> (0 <= f j < N0)%Z) ->
  (forall i j, (0 <= i < t)%Z -> (0 <= j < t)%Z -> f i = f j -> i = j) ->
  (t <= Z.max 0 N0)%Z.
Proof.
  intros f t N0 Ht Hb Hi.
  set (L := map (fun j => f (Z.of_nat j)) (seq 0 (Z.to_nat t))).
  assert (Hnd : NoDup L).
  { apply NoDup_map_NoDup_ForallPairs; [| apply seq_NoDup].
    intros a b Ha Hb' E. apply in_seq in Ha, Hb'. apply Hi in E; lia. }
  assert (Hin : forall z, In z L -> (0 <= z < N0)%Z).
  { intros z Hz. apply in_map_iff in Hz. destruct Hz as (j & <- & Hj). apply in_seq in Hj.
    apply Hb. lia. }
  pose proof (nodup_len N0 L Hnd Hin) as H. unfold L in H. rewrite length_map, length_seq in H. lia.
Qed.

Section Graph.

Variables (n : int) (us vs ws : array int).

Definition N : Z := (φ n).
Definition M : Z := (φ (PArray.length us)).
Definition au (k : Z) : Z := at_ us k.
Definition av (k : Z) : Z := at_ vs k.
Definition aw (k : Z) : Z := Sint63.to_Z (ws.[of_Z k]).

Hypothesis Hn : (1 <= N <= 150)%Z.
Hypothesis HM : (M <= 5000)%Z.
Hypothesis Hlv : PArray.length vs = PArray.length us.
Hypothesis Hlw : PArray.length ws = PArray.length us.
Hypothesis Hend : forall k, (0 <= k < M)%Z -> (0 <= au k < N /\ 0 <= av k < N)%Z.
Hypothesis Hwt : forall k, (0 <= k < M)%Z -> (-1000 <= aw k <= 1000)%Z.

Lemma M_nonneg : (0 <= M)%Z.
Proof. unfold M. pose proof (to_Z_bounded (PArray.length us)). lia. Qed.

(* ------------------------------------------------------------------ *)
(* The edges, and the forward star                                     *)
(* ------------------------------------------------------------------ *)

Definition Ge (a b w : Z) : Prop :=
  exists k, (0 <= k < M)%Z /\ au k = a /\ av k = b /\ aw k = w.

Lemma Ge_bounds : forall a b w, Ge a b w -> (0 <= a < N /\ 0 <= b < N)%Z.
Proof. intros a b w (k & Hk & <- & <- & _). apply Hend. exact Hk. Qed.

Lemma Ge_w : forall a b w, Ge a b w -> (-1000 <= w <= 1000)%Z.
Proof. intros a b w (k & Hk & _ & _ & <-). apply Hwt. exact Hk. Qed.

Fixpoint lastb (a : Z) (c : nat) : Z :=
  match c with
  | O => 0
  | S c' => if Z.eqb (au (Z.of_nat c')) a then (Z.of_nat c' + 1)%Z else lastb a c'
  end.

Definition Lb (a c : Z) : Z := lastb a (Z.to_nat c).

Lemma Lb_succ : forall a c, (0 <= c)%Z ->
  Lb a (c + 1) = if Z.eqb (au c) a then (c + 1)%Z else Lb a c.
Proof.
  intros a c Hc. unfold Lb. rewrite Z2Nat.inj_add by lia. rewrite Nat.add_1_r. simpl.
  rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma Lb_props : forall a c, (0 <= c)%Z ->
  (0 <= Lb a c <= c)%Z /\
  (forall e, Lb a c = (e + 1)%Z -> (0 <= e)%Z ->
     au e = a /\ (e < c)%Z /\ forall e', (e < e' < c)%Z -> au e' <> a) /\
  (Lb a c = 0%Z -> forall e', (0 <= e' < c)%Z -> au e' <> a).
Proof.
  intros a c Hc. pattern c. apply natlike_ind; [| | exact Hc].
  - unfold Lb. simpl. split; [lia | split; intros; lia].
  - intros x Hx (IH1 & IH2 & IH3). unfold Z.succ. rewrite Lb_succ by exact Hx.
    destruct (Z.eqb_spec (au x) a) as [E | E].
    + split; [lia | split].
      * intros e He _. assert (e = x) by lia. subst e. split; [exact E | split; [lia | intros; lia]].
      * intros; lia.
    + split; [lia | split].
      * intros e He He0. destruct (IH2 e He He0) as (A1 & A2 & A3). split; [exact A1 | split; [lia|]].
        intros e' He'. destruct (Z.eq_dec e' x) as [-> | Hne]; [exact E | apply A3; lia].
      * intros H0 e' He'. destruct (Z.eq_dec e' x) as [-> | Hne]; [exact E | apply IH3; [exact H0 | lia]].
Qed.

Lemma build_adj_spec : forall hd nx, build_adj n (PArray.length us) us = (hd, nx) ->
  PArray.length hd = n /\ PArray.length nx = PArray.length us /\
  (forall a, (0 <= a < N)%Z -> at_ hd a = Lb a M) /\
  (forall e, (0 <= e < M)%Z -> at_ nx e = Lb (au e) e).
Proof.
  intros hd nx Hb. unfold build_adj in Hb.
  pose proof (alen_bound_i us) as Bu.
  set (Inv := fun (k : Z) (st : array int * array int) =>
    PArray.length (fst st) = n /\ PArray.length (snd st) = PArray.length us /\
    (forall a, (0 <= a < N)%Z -> at_ (fst st) a = Lb a k) /\
    (forall e, (0 <= e < k)%Z -> at_ (snd st) e = Lb (au e) e)).
  assert (H : Inv (φ (PArray.length us)) (for_loop (adj_step us) 0 (PArray.length us)
                 (PArray.make n 0, PArray.make (PArray.length us) 0))).
  { apply for_loop_inv.
    - change (φ 0) with 0%Z. pose proof (to_Z_bounded (PArray.length us)). lia.
    - change (φ 0) with 0%Z. unfold Inv; simpl.
      split; [apply alen_make_i; unfold N in Hn; lia |].
      split; [apply alen_make_i; lia |].
      split; [intros a Ha; rewrite at_make; reflexivity | intros; lia].
    - intros k [hd0 nx0] Hk (I1 & I2 & I3 & I4). change (φ 0) with 0%Z in Hk.
      simpl in I1, I2, I3, I4. unfold adj_step, Inv; simpl.
      assert (Ha : (0 <= au (φ k) < N)%Z) by (apply Hend; unfold M; lia).
      unfold au in Ha. rewrite at_phi in Ha.
      rewrite !alen_set_i. split; [exact I1 | split; [exact I2 | split]].
      + intros a Ha'. rewrite at_set by (try rewrite I1; unfold N in *; rewrite ?wB_val; lia).
        rewrite Lb_succ by lia. unfold au at 1. rewrite at_phi.
        destruct (Z.eqb_spec a (φ (us.[k]))) as [E | E].
        * subst a. rewrite Z.eqb_refl. apply phi_add1. lia.
        * destruct (Z.eqb_spec (φ (us.[k])) a); [congruence|]. apply I3. exact Ha'.
      + intros e He. rewrite at_set by (try rewrite I2; rewrite ?wB_val; lia).
        destruct (Z.eqb_spec e (φ k)) as [E | E].
        * subst e. rewrite <- (at_phi hd0 (us.[k])).
          replace (au (φ k)) with (φ (us.[k])) by (unfold au; rewrite at_phi; reflexivity).
          apply I3. exact Ha.
        * apply I4. lia. }
  rewrite Hb in H. destruct H as (I1 & I2 & I3 & I4). simpl in *.
  split; [exact I1 | split; [exact I2 | split; [exact I3 | exact I4]]].
Qed.

Lemma chain_spec : forall {S : Type} (nx : array int) (f : int -> S -> S) (x : Z)
  (Inv : Z -> S -> Prop),
  (forall e, (0 <= e < M)%Z -> at_ nx e = Lb (au e) e) ->
  (forall c e s, (0 <= e < c)%Z -> (c <= M)%Z -> Lb x c = (e + 1)%Z -> Inv c s ->
     Inv e (f (of_Z e) s)) ->
  forall cur c s, (0 <= c <= M)%Z -> (φ cur) = Lb x c -> Inv c s ->
  exists c', (0 <= c' <= M)%Z /\ Lb x c' = 0%Z /\ Inv c' (chain_fold nx f cur s).
Proof.
  intros S nx f x Inv Hnx Hstep.
  enough (G : forall z cur (Hacc : Acc (Zwf 0) (φ cur)) c s, (φ cur) = z ->
    (0 <= c <= M)%Z -> (φ cur) = Lb x c -> Inv c s ->
    exists c', (0 <= c' <= M)%Z /\ Lb x c' = 0%Z /\ Inv c' (chain_acc nx f cur s Hacc)).
  { intros cur c s Hc Hcur Hinv. unfold chain_fold. eapply G; eauto. }
  intro z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros cur Hacc c s Hz Hc Hcur Hinv. rewrite chain_acc_eq.
  destruct (bdec (0 <? cur)) as [H0 | H0].
  - cbv zeta. rewrite ltb_spec in H0. change (φ 0) with 0%Z in H0.
    set (e0 := (Lb x c - 1)%Z).
    destruct (Lb_props x c ltac:(lia)) as (L1 & L2 & L3).
    destruct (L2 e0 ltac:(unfold e0; lia) ltac:(unfold e0; lia)) as (A1 & A2 & A3).
    assert (Ee : cur - 1 = of_Z e0).
    { apply phi_inj. rewrite of_Z_phi by (rewrite wB_val; unfold M in *; lia). unfold e0. sia. }
    rewrite Ee.
    assert (Hi : Inv e0 (f (of_Z e0) s)) by (apply (Hstep c); auto; unfold e0; lia).
    assert (Hc' : (φ (nx.[of_Z e0])) = Lb x e0).
    { rewrite <- A1. rewrite <- (Hnx e0 ltac:(unfold e0; lia)). reflexivity. }
    destruct (Lb_props x e0 ltac:(unfold e0; lia)) as (B1 & _ & _).
    destruct (bdec (nx.[of_Z e0] <? cur)) as [Hlt | Hlt].
    + eapply IH; [ | reflexivity | | exact Hc' | exact Hi].
      * unfold Zwf. rewrite <- Hz, Hc'. unfold e0 in *. lia.
      * unfold e0 in *. lia.
    + exfalso. rewrite <- Bool.not_true_iff_false, ltb_spec in Hlt. unfold e0 in *. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in H0. change (φ 0) with 0%Z in H0.
    pose proof (to_Z_bounded cur).
    exists c. split; [exact Hc | split; [lia | exact Hinv]].
Qed.

(* ------------------------------------------------------------------ *)
(* Breadth-first closure                                               *)
(* ------------------------------------------------------------------ *)

Definition RG := R Ge.

Lemma RG_step : forall x a b w, RG x a -> Ge a b w -> RG x b.
Proof. intros x a b w H He. apply (R_trans Ge x a b H). eapply R_edge; eauto. Qed.

Record binv (Snd : Z -> Prop) (mark : array bool) (q : array int) (tl : int) : Prop := {
  bi_lm : PArray.length mark = n;
  bi_lq : PArray.length q = n;
  bi_tl : (0 <= (φ tl) <= N)%Z;
  bi_mq : forall y, (0 <= y < N)%Z ->
            (atb mark y = true <-> exists j, (0 <= j < (φ tl))%Z /\ at_ q j = y);
  bi_qb : forall j, (0 <= j < (φ tl))%Z -> (0 <= at_ q j < N)%Z;
  bi_qi : forall i j, (0 <= i < (φ tl))%Z -> (0 <= j < (φ tl))%Z -> at_ q i = at_ q j -> i = j;
  bi_sd : forall y, (0 <= y < N)%Z -> atb mark y = true -> Snd y
}.

Definition grows (mark : array bool) (q : array int) (tl : int)
                 (mark' : array bool) (q' : array int) (tl' : int) : Prop :=
  ((φ tl) <= (φ tl'))%Z /\ (forall j, (0 <= j < (φ tl))%Z -> at_ q' j = at_ q j) /\
  (forall y, (0 <= y < N)%Z -> atb mark y = true -> atb mark' y = true).

Lemma grows_refl : forall mark q tl, grows mark q tl mark q tl.
Proof. intros. split; [lia | split; auto]. Qed.

Lemma grows_trans : forall m1 q1 t1 m2 q2 t2 m3 q3 t3,
  grows m1 q1 t1 m2 q2 t2 -> grows m2 q2 t2 m3 q3 t3 -> grows m1 q1 t1 m3 q3 t3.
Proof.
  intros m1 q1 t1 m2 q2 t2 m3 q3 t3 (A1 & A2 & A3) (B1 & B2 & B3).
  split; [lia | split].
  - intros j Hj. rewrite B2 by lia. apply A2. exact Hj.
  - intros y Hy H. apply B3; [exact Hy | apply A3; auto].
Qed.

Lemma N_wB : (N < wB)%Z.
Proof. rewrite wB_val. lia. Qed.

Lemma push_spec : forall Snd mark q tl (b : int),
  binv Snd mark q tl -> ((φ b) < N)%Z -> atb mark (φ b) = false -> Snd (φ b) ->
  binv Snd (mark.[b <- true]) (q.[tl <- b]) (tl + 1) /\
  grows mark q tl (mark.[b <- true]) (q.[tl <- b]) (tl + 1) /\
  atb (mark.[b <- true]) (φ b) = true.
Proof.
  intros Snd mark q tl b [L1 L2 T MQ QB QI SD] Hb Hm Hs.
  pose proof (to_Z_bounded b) as Bb. pose proof N_wB as Hw.
  assert (Ht : ((φ tl) < N)%Z).
  { set (f := fun j => if Z.eqb j (φ tl) then (φ b) else at_ q j).
    assert (Hle := inj_bound f ((φ tl) + 1) N ltac:(lia)).
    enough ((φ tl) + 1 <= Z.max 0 N)%Z by lia.
    apply Hle.
    - intros j Hj. unfold f. destruct (Z.eqb_spec j (φ tl)); [lia | apply QB; lia].
    - intros i j Hi Hj. unfold f.
      destruct (Z.eqb_spec i (φ tl)), (Z.eqb_spec j (φ tl)); try lia.
      + intros E. exfalso. assert (atb mark (φ b) = true) by (apply MQ; [lia | exists j; split; [lia | auto]]). congruence.
      + intros E. exfalso. assert (atb mark (φ b) = true) by (apply MQ; [lia | exists i; split; [lia | auto]]). congruence.
      + apply QI; lia. }
  assert (Et : (φ (tl + 1)) = ((φ tl) + 1)%Z) by (apply phi_add1; lia).
  assert (AQ : forall j, (0 <= j < N)%Z -> at_ q.[tl <- b] j = if Z.eqb j (φ tl) then (φ b) else at_ q j)
    by (intros j Hj; apply at_set; [rewrite L2; unfold N in *; lia | lia]).
  assert (AM : forall y, (0 <= y < N)%Z -> atb mark.[b <- true] y = if Z.eqb y (φ b) then true else atb mark y)
    by (intros y Hy; apply atb_set; [rewrite L1; unfold N in *; lia | lia]).
  split; [split | split; [split; [lia | split] |]].
  - rewrite alen_set_b. exact L1.
  - rewrite alen_set_i. exact L2.
  - lia.
  - intros y Hy. rewrite AM by exact Hy. rewrite Et. destruct (Z.eqb_spec y (φ b)) as [E | E].
    + split; [intros _; exists (φ tl); split; [lia|]; rewrite AQ by lia; rewrite Z.eqb_refl; auto | auto].
    + rewrite MQ by exact Hy. split.
      * intros (j & Hj & Ej). exists j. split; [lia|]. rewrite AQ by lia.
        destruct (Z.eqb_spec j (φ tl)); [lia | exact Ej].
      * intros (j & Hj & Ej). rewrite AQ in Ej by lia. destruct (Z.eqb_spec j (φ tl)); [congruence|].
        exists j. split; [lia | exact Ej].
  - intros j Hj. rewrite Et in Hj. rewrite AQ by lia. destruct (Z.eqb_spec j (φ tl)); [lia | apply QB; lia].
  - intros i j Hi Hj. rewrite Et in Hi, Hj. rewrite !AQ by lia.
    destruct (Z.eqb_spec i (φ tl)), (Z.eqb_spec j (φ tl)); try lia.
    + intros E. exfalso. assert (atb mark (φ b) = true) by (apply MQ; [lia | exists j; split; [lia | auto]]). congruence.
    + intros E. exfalso. assert (atb mark (φ b) = true) by (apply MQ; [lia | exists i; split; [lia | auto]]). congruence.
    + apply QI; lia.
  - intros y Hy. rewrite AM by exact Hy. destruct (Z.eqb_spec y (φ b)) as [-> | E]; [auto | apply SD; auto].
  - intros j Hj. rewrite AQ by lia. destruct (Z.eqb_spec j (φ tl)); [lia | reflexivity].
  - intros y Hy H. rewrite AM by exact Hy. destruct (Z.eqb (y) (φ b)); auto.
  - rewrite AM by lia. rewrite Z.eqb_refl. reflexivity.
Qed.

Section Closure.
  Variables (hd nx : array int).
  Hypothesis Hhd : forall a, (0 <= a < N)%Z -> at_ hd a = Lb a M.
  Hypothesis Hnx : forall e, (0 <= e < M)%Z -> at_ nx e = Lb (au e) e.
  Variable seed : array bool.
  Hypothesis Hls : PArray.length seed = n.

  Definition Snd (y : Z) : Prop := exists x, (0 <= x < N)%Z /\ atb seed x = true /\ RG x y.

  Definition seeded (mark : array bool) : Prop :=
    forall x, (0 <= x < N)%Z -> atb seed x = true -> atb mark x = true.

  Definition scanned (mark : array bool) (q : array int) (h : Z) : Prop :=
    forall j, (0 <= j < h)%Z -> forall e, (0 <= e < M)%Z -> au e = at_ q j -> atb mark (av e) = true.

  Lemma seed_phase :
    let '(mark, q, tl) := for_loop (seed_step seed) 0 n (PArray.make n false, PArray.make n 0, 0) in
    binv Snd mark q tl /\ seeded mark.
  Proof.
    set (Inv := fun (a : Z) (st : array bool * array int * int) =>
      let '(mark, q, tl) := st in
      binv Snd mark q tl /\ (forall x, (0 <= x < a)%Z -> atb seed x = true -> atb mark x = true) /\
      (forall y, (0 <= y < N)%Z -> atb mark y = true -> (y < a)%Z)).
    assert (H : Inv (φ n) (for_loop (seed_step seed) 0 n (PArray.make n false, PArray.make n 0, 0))).
    { apply for_loop_inv; change (φ 0) with 0%Z; [unfold N in Hn; lia | |].
      - unfold Inv. split; [split | split].
        + apply alen_make_b. unfold N in Hn; lia.
        + apply alen_make_i. unfold N in Hn; lia.
        + change (φ 0) with 0%Z. lia.
        + intros y Hy. rewrite atb_make. change (φ 0) with 0%Z. split; [discriminate | intros (j & Hj & _); lia].
        + intros j Hj. change (φ 0) with 0%Z in Hj. lia.
        + intros i j Hi. change (φ 0) with 0%Z in Hi. lia.
        + intros y Hy Hm. rewrite atb_make in Hm. discriminate.
        + intros x Hx. lia.
        + intros y Hy Hm. rewrite atb_make in Hm. discriminate.
      - intros a [[mark q] tl] Ha (BI & SE & LT). unfold seed_step.
        destruct (seed.[a]) eqn:Es.
        + assert (Hm : atb mark (φ a) = false).
          { destruct (atb mark (φ a)) eqn:E; [| reflexivity]. exfalso.
            pose proof (LT (φ a) ltac:(unfold N; lia) E). lia. }
          destruct (push_spec Snd mark q tl a BI ltac:(unfold N; lia) Hm) as (BI' & (G1 & G2 & G3) & Hma).
          { exists (φ a). split; [unfold N; lia | split; [rewrite atb_phi; exact Es | apply R_refl]]. }
          split; [exact BI' | split].
          * intros x Hx Hs. destruct (Z.eq_dec x (φ a)) as [-> | Hne]; [exact Hma|].
            apply G3; [unfold N in *; lia | apply SE; [lia | exact Hs]].
          * intros y Hy Hm'. rewrite atb_set in Hm' by (try rewrite (bi_lm _ _ _ _ BI); unfold N in *; rewrite ?wB_val; lia).
            destruct (Z.eqb_spec y (φ a)); [lia|]. pose proof (LT y Hy Hm'). lia.
        + split; [exact BI | split].
          * intros x Hx Hs. destruct (Z.eq_dec x (φ a)) as [-> | Hne]; [rewrite atb_phi in Hs; congruence|].
            apply SE; [lia | exact Hs].
          * intros y Hy Hm'. pose proof (LT y Hy Hm'). lia. }
    destruct (for_loop (seed_step seed) 0 n (PArray.make n false, PArray.make n 0, 0)) as [[mark q] tl].
    destruct H as (BI & SE & _). split; [exact BI|]. intros x Hx. apply SE. exact Hx.
  Qed.

  Lemma visit_chain : forall mark q tl (x : Z),
    binv Snd mark q tl -> (0 <= x < N)%Z -> atb mark x = true ->
    let '(mark', q', tl') := chain_fold nx (bfs_visit vs) (hd.[of_Z x]) (mark, q, tl) in
    binv Snd mark' q' tl' /\ grows mark q tl mark' q' tl' /\
    (forall e, (0 <= e < M)%Z -> au e = x -> atb mark' (av e) = true).
  Proof.
    intros mark q tl x BI Hx Hmx.
    set (Inv := fun (c : Z) (st : array bool * array int * int) =>
      let '(mark', q', tl') := st in
      binv Snd mark' q' tl' /\ grows mark q tl mark' q' tl' /\
      (forall e, (c <= e < M)%Z -> au e = x -> atb mark' (av e) = true)).
    destruct (chain_spec nx (bfs_visit vs) x Inv Hnx) with (cur := hd.[of_Z x]) (c := M)
        (s := (mark, q, tl)) as (c' & Hc' & Hl0 & HI).
    - intros c e [[m1 q1] t1] He Hc HL (B1 & G1 & P1). unfold bfs_visit.
      destruct (Lb_props x c ltac:(lia)) as (_ & L2 & _).
      destruct (L2 e HL ltac:(lia)) as (A1 & A2 & A3).
      destruct (Hend e ltac:(lia)) as [_ Hv].
      assert (Ev : (φ (vs.[of_Z e])) = av e) by reflexivity.
      destruct (m1.[vs.[of_Z e]]) eqn:Em.
      + split; [exact B1 | split; [exact G1|]].
        intros e' He' Hx'. destruct (Z.eq_dec e' e) as [-> | Hne].
        * rewrite <- Ev, atb_phi. exact Em.
        * apply P1; [| exact Hx']. destruct (Z_lt_le_dec e' c); [| lia].
          exfalso. apply (A3 e'); [lia | exact Hx'].
      + rewrite <- atb_phi, Ev in Em.
        assert (Hs : Snd (av e)).
        { destruct (bi_sd _ _ _ _ B1 x Hx ltac:(apply (proj2 (proj2 G1)); auto)) as (x0 & Hx0 & Hs0 & Hr).
          exists x0. split; [exact Hx0 | split; [exact Hs0|]].
          apply (RG_step x0 x (av e) (aw e) Hr). exists e. split; [lia | auto]. }
        rewrite <- Ev in Em, Hs.
        destruct (push_spec Snd m1 q1 t1 (vs.[of_Z e]) B1 ltac:(lia) Em Hs) as (B2 & G2 & Hm2).
        split; [exact B2 | split; [eapply grows_trans; eauto |]].
        intros e' He' Hx'. destruct (Z.eq_dec e' e) as [-> | Hne].
        * exact Hm2.
        * destruct G2 as (_ & _ & G2). apply G2; [apply Hend; lia |]. apply P1; [| exact Hx'].
          destruct (Z_lt_le_dec e' c); [| lia]. exfalso. apply (A3 e'); [lia | exact Hx'].
    - unfold M. pose proof (to_Z_bounded (PArray.length us)). lia.
    - rewrite <- (Hhd x Hx). reflexivity.
    - split; [exact BI | split; [apply grows_refl | intros; lia]].
    - destruct (chain_fold nx (bfs_visit vs) hd.[of_Z x] (mark, q, tl)) as [[m' q'] t'].
      destruct HI as (B' & G' & P'). split; [exact B' | split; [exact G'|]].
      intros e He Hx'. destruct (Lb_props x c' ltac:(lia)) as (_ & _ & L3).
      apply P'; [| exact Hx']. destruct (Z_lt_le_dec e c'); [| lia].
      exfalso. apply (L3 Hl0 e); [lia | exact Hx'].
  Qed.

  Lemma bfs_main : forall z h mark q tl H, gap n h = z ->
    binv Snd mark q tl -> (0 <= (φ h) <= (φ tl))%Z -> seeded mark -> scanned mark q (φ h) ->
    let mk := bfs_acc hd nx vs n h (mark, q, tl) H in
    PArray.length mk = n /\ seeded mk /\
    (forall y, (0 <= y < N)%Z -> atb mk y = true -> Snd y) /\
    (forall e, (0 <= e < M)%Z -> atb mk (au e) = true -> atb mk (av e) = true).
  Proof.
    intro z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros h mark q tl H Hz BI Hh SE SC. cbv zeta. rewrite bfs_acc_eq.
    pose proof (bi_tl _ _ _ _ BI) as Tl.
    destruct (bdec ((h <? tl) && (h <? n))) as [Hc | Hc].
    - pose proof Hc as Hc'. apply andb_prop in Hc'. destruct Hc' as [C1 C2].
      rewrite ltb_spec in C1, C2. cbv zeta.
      set (x := at_ q (φ h)).
      assert (Hx : (0 <= x < N)%Z) by (apply (bi_qb _ _ _ _ BI); lia).
      assert (Hmx : atb mark x = true) by (apply (bi_mq _ _ _ _ BI); [exact Hx | exists (φ h); split; [lia | reflexivity]]).
      assert (Ex : q.[h] = of_Z x) by (unfold x, at_; rewrite !of_to_Z; reflexivity).
      rewrite Ex.
      pose proof (visit_chain mark q tl x BI Hx Hmx) as VC.
      destruct (chain_fold nx (bfs_visit vs) hd.[of_Z x] (mark, q, tl)) as [[m' q'] t'] eqn:Ech.
      destruct VC as (B' & (G1 & G2 & G3) & P').
      assert (Eh : (φ (h + 1)) = ((φ h) + 1)%Z) by (apply phi_add1; unfold N in *; lia).
      eapply IH; [ | reflexivity | exact B' | | | ].
      + rewrite <- Hz. apply (bfs_dec n h tl Hc).
      + lia.
      + intros y Hy Hs. apply G3; [exact Hy | apply SE; auto].
      + rewrite Eh. intros j Hj e He Hq. rewrite G2 in Hq by lia.
        destruct (Z.eq_dec j (φ h)) as [-> | Hne].
        * apply P'; [exact He | exact Hq].
        * apply G3; [apply Hend; exact He|]. apply (SC j); [lia | exact He | exact Hq].
    - assert (Hht : (φ h) = (φ tl)).
      { destruct (h <? tl) eqn:E1; [| rewrite <- Bool.not_true_iff_false, ltb_spec in E1; lia].
        destruct (h <? n) eqn:E2; [discriminate|]. rewrite <- Bool.not_true_iff_false, ltb_spec in E2.
        rewrite ltb_spec in E1. unfold N in *. lia. }
      split; [exact (bi_lm _ _ _ _ BI) | split; [exact SE | split; [apply (bi_sd _ _ _ _ BI)|]]].
      intros e He Hm. destruct (Hend e He) as [Hu _].
      destruct (proj1 (bi_mq _ _ _ _ BI (au e) Hu) Hm) as (j & Hj & Ej).
      apply (SC j); [lia | exact He | symmetry; exact Ej].
  Qed.

  Lemma closure_spec :
    let mk := closure n hd nx vs seed in
    PArray.length mk = n /\
    forall y, (0 <= y < N)%Z ->
      (atb mk y = true <-> exists x, (0 <= x < N)%Z /\ atb seed x = true /\ RG x y).
  Proof.
    cbv zeta. unfold closure. pose proof seed_phase as SP.
    destruct (for_loop (seed_step seed) 0 n (PArray.make n false, PArray.make n 0, 0)) as [[mark q] tl].
    destruct SP as [BI SE].
    destruct (bfs_main _ 0 mark q tl (Zwf_well_founded 0 (gap n 0)) eq_refl BI
                ltac:(change (φ 0) with 0%Z; pose proof (bi_tl _ _ _ _ BI); lia) SE
                ltac:(intros j Hj; change (φ 0) with 0%Z in Hj; lia)) as (L & S1 & S2 & S3).
    split; [exact L|]. intros y Hy. split; [apply S2; exact Hy|].
    intros (x & Hx & Hs & (c & Lw & Hw)).
    assert (G : forall y c Lw, pw Ge x y c Lw -> atb (bfs_acc hd nx vs n 0 (mark, q, tl) (Zwf_well_founded 0 (gap n 0))) y = true).
    { intros y' c' Lw' Hw'. induction Hw' as [| v v' w c'' L'' Hp IHp He].
      - apply S1; auto.
      - destruct He as (k & Hk & <- & <- & _). apply S3; [exact Hk | exact IHp]. }
    exact (G y c Lw Hw).
  Qed.
End Closure.

(* ------------------------------------------------------------------ *)
(* The reachability matrix                                             *)
(* ------------------------------------------------------------------ *)

Lemma idx_phi : forall s v : int, (0 <= (φ s) < N)%Z -> (0 <= (φ v) < N)%Z ->
  (φ (s * n + v)) = ((φ s) * N + (φ v))%Z.
Proof.
  intros s v Hs Hv. unfold N in *.
  assert (H1 : ((φ s) * (φ n) + (φ v) < 22650)%Z) by nia.
  rewrite add_spec, mul_spec. rewrite (Z.mod_small ((φ s) * (φ n))) by (rewrite wB_val; nia).
  apply Z.mod_small. rewrite wB_val. nia.
Qed.

Lemma idx_bound : forall a b, (0 <= a < N)%Z -> (0 <= b < N)%Z -> (0 <= a * N + b < N * N)%Z.
Proof. intros a b Ha Hb. nia. Qed.

Lemma idx_inj : forall a1 b1 a2 b2, (0 <= b1 < N)%Z -> (0 <= b2 < N)%Z ->
  (a1 * N + b1 = a2 * N + b2)%Z -> a1 = a2 /\ b1 = b2.
Proof.
  intros a1 b1 a2 b2 H1 H2 E.
  assert (a1 = a2) by (apply Z.le_antisymm; nia). subst. lia.
Qed.

Lemma nn_phi : (φ (n * n)) = (N * N)%Z.
Proof. unfold N in *. rewrite mul_spec. apply Z.mod_small. rewrite wB_val. nia. Qed.

Section Reach.
  Variables (hd nx : array int).
  Hypothesis Hhd : forall a, (0 <= a < N)%Z -> at_ hd a = Lb a M.
  Hypothesis Hnx : forall e, (0 <= e < M)%Z -> at_ nx e = Lb (au e) e.

  Lemma reach_matrix_spec :
    let Rm := reach_matrix n hd nx vs in
    PArray.length Rm = n * n /\
    forall s v, (0 <= s < N)%Z -> (0 <= v < N)%Z -> (atb Rm (s * N + v) = true <-> RG s v).
  Proof.
    cbv zeta. unfold reach_matrix.
    assert (Hnn : PArray.length (PArray.make (n * n) false) = n * n)
      by (apply alen_make_b; rewrite nn_phi; nia).
    set (Inv := fun (s : Z) (r : array bool) => PArray.length r = n * n /\
       forall s' v, (0 <= s' < s)%Z -> (0 <= v < N)%Z -> (atb r (s' * N + v) = true <-> RG s' v)).
    enough (H : Inv (φ n) (for_loop (reach_row n hd nx vs) 0 n (PArray.make (n * n) false))).
    { destruct H as [H1 H2]. split; [exact H1|]. intros s v Hs Hv. apply H2; [unfold N in *; lia | exact Hv]. }
    apply for_loop_inv; change (φ 0) with 0%Z; [unfold N in *; lia | split; [exact Hnn | intros; lia] |].
    intros s r Hs [L1 L2]. unfold reach_row.
    set (seed := (PArray.make n false).[s <- true]).
    assert (Hls : PArray.length seed = n) by (unfold seed; rewrite alen_set_b; apply alen_make_b; unfold N in *; lia).
    destruct (closure_spec hd nx Hhd Hnx seed Hls) as [Lr Cr].
    set (row := closure n hd nx vs seed) in *.
    assert (Hrow : forall y, (0 <= y < N)%Z -> (atb row y = true <-> RG (φ s) y)).
    { intros y Hy. rewrite Cr by exact Hy. split.
      - intros (x & Hx & Hsx & Hr). unfold seed in Hsx. rewrite atb_set in Hsx
          by (try rewrite alen_make_b; unfold N in *; rewrite ?wB_val; lia).
        destruct (Z.eqb_spec x (φ s)) as [-> | E]; [exact Hr | rewrite atb_make in Hsx; discriminate].
      - intros Hr. exists (φ s). split; [unfold N in *; lia | split; [| exact Hr]].
        unfold seed. rewrite atb_set by (try rewrite alen_make_b; unfold N in *; rewrite ?wB_val; lia).
        rewrite Z.eqb_refl. reflexivity. }
    set (Inv2 := fun (v : Z) (r' : array bool) => PArray.length r' = n * n /\
       (forall s' v', (0 <= s' < (φ s))%Z -> (0 <= v' < N)%Z -> atb r' (s' * N + v') = atb r (s' * N + v')) /\
       (forall v', (0 <= v' < v)%Z -> atb r' ((φ s) * N + v') = atb row v')).
    assert (H2 : Inv2 (φ n) (for_loop (copy_step n s row) 0 n r)).
    { apply for_loop_inv; change (φ 0) with 0%Z; [unfold N in *; lia | split; [exact L1 | split; [auto | intros; lia]] |].
      intros v r' Hv (M1 & M2 & M3). unfold copy_step.
      assert (Ei := idx_phi s v ltac:(unfold N in *; lia) ltac:(unfold N in *; lia)).
      assert (Hb : ((φ s) * N + (φ v) < N * N)%Z) by (apply idx_bound; unfold N in *; lia).
      assert (Hw : (N * N < wB)%Z) by (rewrite wB_val; clear - Hn; nia).
      assert (AS : forall z, (0 <= z < N * N)%Z ->
                 atb r'.[s * n + v <- row.[v]] z = if Z.eqb z ((φ s) * N + (φ v)) then row.[v] else atb r' z).
      { intros z Hz. rewrite atb_set by (rewrite ?M1, ?nn_phi, ?Ei; lia). rewrite Ei. reflexivity. }
      split; [rewrite alen_set_b; exact M1 | split].
      - intros s' v' Hs' Hv'. rewrite AS by (apply idx_bound; unfold N in *; lia).
        destruct (Z.eqb_spec (s' * N + v') ((φ s) * N + (φ v))) as [E | E];
          [apply idx_inj in E; unfold N in *; lia | apply M2; auto].
      - intros v' Hv'. rewrite AS by (apply idx_bound; unfold N in *; lia).
        destruct (Z.eqb_spec ((φ s) * N + v') ((φ s) * N + (φ v))).
        + assert (v' = (φ v)) by lia. subst v'. rewrite atb_phi. reflexivity.
        + apply M3. lia. }
    destruct H2 as (M1 & M2 & M3). split; [exact M1|].
    intros s' v Hs' Hv. destruct (Z.eq_dec s' (φ s)) as [-> | Hne].
    - rewrite M3 by (unfold N in *; lia). apply Hrow. exact Hv.
    - rewrite M2 by lia. apply L2; [lia | exact Hv].
  Qed.
End Reach.

(* ------------------------------------------------------------------ *)
(* Bellman-Ford over a filtered edge set                               *)
(* ------------------------------------------------------------------ *)

Definition sat (t : array int) (z : Z) : Z := Sint63.to_Z (t.[of_Z z]).

Lemma sat_set : forall (t : array int) (k x : int) (z : Z),
  ((φ k) < (φ (PArray.length t)))%Z -> (0 <= z < wB)%Z ->
  sat (t.[k <- x]) z = if Z.eqb z (φ k) then Sint63.to_Z x else sat t z.
Proof.
  intros t k x z Hk Hz. unfold sat.
  destruct (Z.eqb_spec z (φ k)) as [E | E].
  - replace (of_Z z) with k by (symmetry; apply of_Z_eq; auto).
    rewrite aget_set_same_i; [reflexivity|]. rewrite ltb_spec. exact Hk.
  - rewrite aget_set_other_i; [reflexivity|]. intro F. apply E. apply of_Z_eq; auto.
Qed.

Lemma sat_phi : forall (t : array int) (k : int), sat t (φ k) = Sint63.to_Z (t.[k]).
Proof. intros t k. unfold sat. rewrite of_to_Z. reflexivity. Qed.

Lemma M_wB : (M < 4194304)%Z.
Proof. lia. Qed.

Lemma au_phi : forall k : int, au (φ k) = (φ (us.[k])).
Proof. intros k. unfold au. apply at_phi. Qed.
Lemma av_phi : forall k : int, av (φ k) = (φ (vs.[k])).
Proof. intros k. unfold av. apply at_phi. Qed.
Lemma aw_phi : forall k : int, aw (φ k) = Sint63.to_Z (ws.[k]).
Proof. intros k. unfold aw. rewrite of_to_Z. reflexivity. Qed.

Section BF.
  Variable keep : int -> bool.
  Variable P : Z -> Z -> Prop.
  Hypothesis Hkeep : forall k, (0 <= k < M)%Z -> (keep (of_Z k) = true <-> P (au k) (av k)).

  Definition Gf (a b w : Z) : Prop := Ge a b w /\ P a b.

  Definition bf_walk (h : array int) : Prop :=
    forall v, (0 <= v < N)%Z -> exists x c L, pw Gf x v c L /\ c = sat h v.
  Definition bf_bound (h : array int) (t : Z) : Prop :=
    forall v, (0 <= v < N)%Z -> (- 1000 * t <= sat h v <= 0)%Z.
  Definition bf_opt (h : array int) (r : Z) : Prop :=
    forall v x c L, (0 <= v < N)%Z -> pw Gf x v c L -> (Z.of_nat (List.length L) <= r + 1)%Z -> (sat h v <= c)%Z.
  Definition bf_last (h : array int) (r k : Z) : Prop :=
    forall j x c L, (0 <= j < k)%Z -> P (au j) (av j) -> pw Gf x (au j) c L ->
      (Z.of_nat (List.length L) <= r + 1)%Z -> (sat h (av j) <= c + aw j)%Z.

  Lemma bf_spec :
    let h := bf n (PArray.length us) us vs ws keep in
    PArray.length h = n /\ bf_walk h /\ bf_bound h (N * M) /\ bf_opt h N.
  Proof.
    cbv zeta. unfold bf.
    pose proof M_nonneg as HM0.
    set (Inv := fun (r : Z) (h : array int) => PArray.length h = n /\ bf_walk h /\
                  bf_bound h (r * M) /\ bf_opt h r).
    enough (H : Inv (φ n) (for_loop (bf_round (PArray.length us) us vs ws keep) 0 n (PArray.make n 0)))
      by (destruct H as (A & B & C & D); unfold N; auto).
    apply for_loop_inv; change (φ 0) with 0%Z; [unfold N in *; lia | |].
    - split; [apply alen_make_i; unfold N in *; lia | split; [| split]].
      + intros v Hv. exists v, 0%Z, [v]. split; [constructor | unfold sat; rewrite aget_make_i; reflexivity].
      + intros v Hv. unfold sat. rewrite aget_make_i. change (Sint63.to_Z 0) with 0%Z. lia.
      + intros v x c L Hv Hw HL. destruct Hw as [| v0 v' w c0 L0 Hw He].
        * unfold sat. rewrite aget_make_i. change (Sint63.to_Z 0) with 0%Z. lia.
        * simpl in HL. pose proof (pw_len_pos _ _ _ _ _ Hw). lia.
    - intros r h0 Hr (I1 & I2 & I3 & I4). unfold bf_round.
      set (K := fun (k : Z) (h : array int) => PArray.length h = n /\ bf_walk h /\
                  bf_bound h ((φ r) * M + k) /\ bf_opt h (φ r) /\ bf_last h (φ r) k /\
                  forall v, (0 <= v < N)%Z -> (sat h v <= sat h0 v)%Z).
      assert (HK : K (φ (PArray.length us)) (for_loop (bf_edge us vs ws keep) 0 (PArray.length us) h0)).
      { apply for_loop_inv; change (φ 0) with 0%Z; [unfold M in *; lia | |].
        - split; [exact I1 | split; [exact I2 | split; [rewrite Z.add_0_r; exact I3 | split; [exact I4 | split]]]].
          + intros j x c L Hj. lia.
          + intros; lia.
        - intros k h Hk (K1 & K2 & K3 & K4 & K5 & K6). unfold bf_edge.
          assert (Hk' : (0 <= (φ k) < M)%Z) by (unfold M; lia).
          destruct (Hend (φ k) Hk') as [Ha Hb]. pose proof (Hwt (φ k) Hk') as Hw.
          rewrite au_phi in Ha. rewrite av_phi in Hb. rewrite aw_phi in Hw.
          pose proof N_wB as HNw.
          assert (Hlenh : (N <= (φ (PArray.length h)))%Z) by (rewrite K1; unfold N; lia).
          assert (Ba := K3 _ Ha). rewrite sat_phi in Ba.
          assert (Bb := K3 _ Hb). rewrite sat_phi in Bb.
          assert (Hrt : ((φ r) * M + (φ k) <= 150 * 5000)%Z) by (unfold N in *; nia).
          assert (Esum : Sint63.to_Z (h.[us.[k]] + ws.[k]) = (Sint63.to_Z (h.[us.[k]]) + Sint63.to_Z (ws.[k]))%Z)
            by (apply s_add; lia).
          assert (Hkk : keep k = true <-> P (φ (us.[k])) (φ (vs.[k]))).
          { rewrite <- au_phi, <- av_phi, <- (Hkeep (φ k) Hk'). rewrite of_to_Z. reflexivity. }
          (* the common facts after the step, for an array h' *)
          assert (Hmono_last : forall h', (forall v, (0 <= v < N)%Z -> (sat h' v <= sat h v)%Z) ->
              bf_last h' (φ r) (φ k) /\ bf_opt h' (φ r) /\
              (forall v, (0 <= v < N)%Z -> (sat h' v <= sat h0 v)%Z)).
          { intros h' Hm. split; [| split].
            - intros j x c L Hj Hp Hwk HL. destruct (Hend j ltac:(lia)) as [_ Hvj].
              pose proof (Hm _ Hvj). pose proof (K5 j x c L Hj Hp Hwk HL). lia.
            - intros v x c L Hv Hwk HL. pose proof (Hm _ Hv). pose proof (K4 v x c L Hv Hwk HL). lia.
            - intros v Hv. pose proof (Hm _ Hv). pose proof (K6 _ Hv). lia. }
          destruct (keep k) eqn:Ek.
          + destruct (Sint63.ltb (h.[us.[k]] + ws.[k]) h.[vs.[k]]) eqn:El.
            * rewrite s_ltb, Esum in El.
              assert (AS : forall z, (0 <= z < N)%Z -> sat h.[vs.[k] <- h.[us.[k]] + ws.[k]] z =
                         if Z.eqb z (φ (vs.[k])) then (Sint63.to_Z (h.[us.[k]]) + Sint63.to_Z (ws.[k]))%Z
                         else sat h z)
                by (intros z Hz; rewrite sat_set by lia; rewrite Esum; reflexivity).
              assert (Hm : forall v, (0 <= v < N)%Z -> (sat h.[vs.[k] <- (h.[us.[k]] + ws.[k])%uint63] v <= sat h v)%Z).
              { intros v Hv. rewrite AS by exact Hv. destruct (Z.eqb_spec v (φ (vs.[k]))) as [-> | _]; [rewrite sat_phi; lia | lia]. }
              destruct (Hmono_last _ Hm) as (L1 & L2 & L3).
              split; [rewrite alen_set_i; exact K1 | split; [| split; [| split; [exact L2 | split; [| exact L3]]]]].
              -- intros v Hv. rewrite AS by exact Hv. destruct (Z.eqb_spec v (φ (vs.[k]))) as [-> | _]; [| apply K2; exact Hv].
                 destruct (K2 _ Ha) as (x & c & L & Hwk & Hc). exists x, (c + Sint63.to_Z (ws.[k]))%Z, ((φ (vs.[k])) :: L).
                 split; [| rewrite Hc, sat_phi; reflexivity].
                 econstructor; [exact Hwk |]. split; [| apply Hkk; reflexivity].
                 exists (φ k). split; [exact Hk' | split; [apply au_phi | split; [apply av_phi | apply aw_phi]]].
              -- intros v Hv. rewrite AS by exact Hv. destruct (Z.eqb_spec v (φ (vs.[k]))) as [-> | _].
                 ++ split; [| lia]. nia.
                 ++ pose proof (K3 v Hv). nia.
              -- intros j x c L Hj Hp Hwk HL. destruct (Z.eq_dec j (φ k)) as [-> | Hne].
                 ++ rewrite AS by (rewrite av_phi; lia). rewrite av_phi, Z.eqb_refl, aw_phi.
                    rewrite au_phi in Hwk. pose proof (K4 _ x c L Ha Hwk HL) as Ho. rewrite sat_phi in Ho. lia.
                 ++ apply (L1 j x c L); [lia | exact Hp | exact Hwk | exact HL].
            * rewrite <- Bool.not_true_iff_false, s_ltb, Esum in El.
              destruct (Hmono_last h ltac:(intros; lia)) as (L1 & L2 & L3).
              split; [exact K1 | split; [exact K2 | split; [| split; [exact L2 | split; [| exact L3]]]]].
              -- intros v Hv. pose proof (K3 v Hv). nia.
              -- intros j x c L Hj Hp Hwk HL. destruct (Z.eq_dec j (φ k)) as [-> | Hne].
                 ++ rewrite av_phi, aw_phi. rewrite au_phi in Hwk.
                    pose proof (K4 _ x c L Ha Hwk HL) as Ho. rewrite sat_phi in Ho. rewrite sat_phi. lia.
                 ++ apply (L1 j x c L); [lia | exact Hp | exact Hwk | exact HL].
          + destruct (Hmono_last h ltac:(intros; lia)) as (L1 & L2 & L3).
            split; [exact K1 | split; [exact K2 | split; [| split; [exact L2 | split; [| exact L3]]]]].
            -- intros v Hv. pose proof (K3 v Hv). nia.
            -- intros j x c L Hj Hp Hwk HL. destruct (Z.eq_dec j (φ k)) as [-> | Hne].
               ++ exfalso. rewrite au_phi, av_phi in Hp. apply Hkk in Hp. congruence.
               ++ apply (L1 j x c L); [lia | exact Hp | exact Hwk | exact HL]. }
      destruct HK as (K1 & K2 & K3 & K4 & K5 & _).
      split; [exact K1 | split; [exact K2 | split]].
      + intros v Hv. pose proof (K3 v Hv). fold M in *. nia.
      + intros v x c L Hv Hwk HL. destruct Hwk as [| a v' w c0 L0 Hwk He].
        * apply (K4 x x 0%Z [x] Hv (pw_nil _ _)). simpl. lia.
        * change (List.length (v' :: L0)) with (S (List.length L0)) in HL.
          destruct He as ((j & Hj & Eu & Ev & Ew) & Hp). subst a v' w.
          apply (K5 j x c0 L0); [fold M; lia | exact Hp | exact Hwk | lia].
  Qed.
End BF.

(* ------------------------------------------------------------------ *)
(* Generic walk facts on the graph                                     *)
(* ------------------------------------------------------------------ *)

Lemma rev_reach : forall (E : Z -> Z -> Z -> Prop), (forall a b w, E a b w -> RG b a) ->
  forall x y c L, pw E x y c L -> RG y x.
Proof.
  intros E HE x y c L H. induction H as [| v v' w c L H IH He]; [apply R_refl|].
  apply (R_trans Ge v' v x); [eapply HE; eauto | exact IH].
Qed.

Lemma R_mono : forall (E : Z -> Z -> Z -> Prop), (forall a b w, E a b w -> Ge a b w) ->
  forall x y, R E x y -> RG x y.
Proof. intros E HE x y (c & L & H). exists c, L. eapply pw_mono; eauto. Qed.

(* a negative closed walk at a, reachable from u and reaching v, gives
   walks from u to v of arbitrarily low cost *)
Lemma Z_to_nat_nonpos : forall z, (z <= 0)%Z -> Z.to_nat z = O.
Proof. intros z H. destruct z; simpl; auto; lia. Qed.

Lemma neg_loop_short : forall a u v c0 L0, pw Ge a a c0 L0 -> (c0 < 0)%Z ->
  RG u a -> RG a v -> forall lo, exists c L, pw Ge u v c L /\ (c < lo)%Z.
Proof.
  intros a u v c0 L0 Hl Hc (A & LA & HA) (B & LB & HB) lo.
  destruct (pw_iter Ge a c0 L0 Hl (Z.to_nat (A + B - lo + 1))) as [LK HK].
  destruct (pw_app Ge a a _ LK HK u A LA HA) as [L1 H1].
  destruct (pw_app Ge a v B LB HB u _ L1 H1) as [L2 H2].
  eexists; eexists; split; [exact H2|].
  destruct (Z_le_gt_dec (A + B - lo + 1) 0) as [Hle | Hgt].
  - rewrite (Z_to_nat_nonpos _ Hle). lia.
  - rewrite Z2Nat.id by lia. nia.
Qed.

Lemma Gf_Ge : forall P a b w, Gf P a b w -> Ge a b w.
Proof. intros P a b w [H _]. exact H. Qed.

Lemma Gf_bounds : forall P a b w, Gf P a b w -> (0 <= a < N /\ 0 <= b < N)%Z.
Proof. intros P a b w [H _]. eapply Ge_bounds; eauto. Qed.

(* a walk without repeated vertex has at most N vertices *)
Lemma nodup_walk_len : forall (E : Z -> Z -> Z -> Prop),
  (forall a b w, E a b w -> (0 <= a < N /\ 0 <= b < N)%Z) ->
  forall x y c L, pw E x y c L -> (0 <= x < N)%Z -> NoDup L -> (Z.of_nat (List.length L) <= N)%Z.
Proof.
  intros E HE x y c L H Hx Hnd.
  pose proof (nodup_len N L Hnd (pw_vertices E N HE x y c L H Hx)). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The bad vertices and the potentials                                 *)
(* ------------------------------------------------------------------ *)

Section Potentials.
  Variables (hd nx : array int).
  Hypothesis Hhd : forall a, (0 <= a < N)%Z -> at_ hd a = Lb a M.
  Hypothesis Hnx : forall e, (0 <= e < M)%Z -> at_ nx e = Lb (au e) e.

  Definition Rm := reach_matrix n hd nx vs.

  Lemma Rm_spec : forall s v, (0 <= s < N)%Z -> (0 <= v < N)%Z -> (atb Rm (s * N + v) = true <-> RG s v).
  Proof. apply (reach_matrix_spec hd nx Hhd Hnx). Qed.

  Lemma Rm_len : PArray.length Rm = n * n.
  Proof. apply (reach_matrix_spec hd nx Hhd Hnx). Qed.

  Lemma Rm_get : forall s v : int, (0 <= (φ s) < N)%Z -> (0 <= (φ v) < N)%Z ->
    (Rm.[s * n + v] = true <-> RG (φ s) (φ v)).
  Proof.
    intros s v Hs Hv. rewrite <- atb_phi, idx_phi by auto. apply Rm_spec; auto.
  Qed.

  Definition keep1 (k : int) : bool := Rm.[vs.[k] * n + us.[k]].
  Definition P1 (a b : Z) : Prop := RG b a.

  Lemma keep1_spec : forall k, (0 <= k < M)%Z -> (keep1 (of_Z k) = true <-> P1 (au k) (av k)).
  Proof.
    intros k Hk. destruct (Hend k Hk) as [Ha Hb].
    unfold keep1, P1. replace (au k) with (φ (us.[of_Z k])) by reflexivity.
    replace (av k) with (φ (vs.[of_Z k])) by reflexivity.
    apply Rm_get; assumption.
  Qed.

  Definition h1 := bf n (PArray.length us) us vs ws keep1.

  Lemma h1_spec : PArray.length h1 = n /\ bf_walk P1 h1 /\ bf_bound h1 (N * M) /\ bf_opt P1 h1 N.
  Proof. apply (bf_spec keep1 P1 keep1_spec). Qed.

  Definition bad := for_loop (bad_step n us vs ws Rm h1) 0 (PArray.length us) (PArray.make n false).

  Definition viol (k : Z) : Prop :=
    RG (av k) (au k) /\ (sat h1 (au k) + aw k < sat h1 (av k))%Z.

  Lemma bad_spec : PArray.length bad = n /\
    forall a, (0 <= a < N)%Z ->
      (atb bad a = true <-> exists k, (0 <= k < M)%Z /\ au k = a /\ viol k).
  Proof.
    destruct h1_spec as (H1 & _ & H3 & _).
    unfold bad.
    set (Inv := fun (k : Z) (b : array bool) => PArray.length b = n /\
      forall a, (0 <= a < N)%Z -> (atb b a = true <-> exists j, (0 <= j < k)%Z /\ au j = a /\ viol j)).
    enough (H : Inv M (for_loop (bad_step n us vs ws Rm h1) 0 (PArray.length us) (PArray.make n false)))
      by exact H.
    change M with (φ (PArray.length us)).
    apply for_loop_inv; change (φ 0) with 0%Z; [apply M_nonneg | |].
    - split; [apply alen_make_b; unfold N in *; lia|]. intros a Ha. rewrite atb_make.
      split; [discriminate | intros (j & Hj & _); lia].
    - intros k b Hk [L1 L2]. unfold bad_step.
      assert (Hk' : (0 <= (φ k) < M)%Z) by (unfold M; lia).
      destruct (Hend (φ k) Hk') as [Ha Hb]. pose proof (Hwt (φ k) Hk') as Hw.
      rewrite au_phi in Ha. rewrite av_phi in Hb. rewrite aw_phi in Hw.
      pose proof (H3 _ Ha) as Ba. pose proof (H3 _ Hb) as Bb. rewrite sat_phi in Ba, Bb.
      assert (Hnm : (N * M <= 150 * 5000)%Z) by nia.
      assert (Esum : Sint63.to_Z (h1.[us.[k]] + ws.[k]) = (Sint63.to_Z (h1.[us.[k]]) + Sint63.to_Z (ws.[k]))%Z)
        by (apply s_add; nia).
      assert (Hv : viol (φ k) <-> (Rm.[vs.[k] * n + us.[k]] && Sint63.ltb (h1.[us.[k]] + ws.[k]) h1.[vs.[k]]) = true).
      { unfold viol. rewrite andb_true_iff, s_ltb, Esum, Rm_get by lia.
        rewrite au_phi, av_phi, aw_phi, !sat_phi. reflexivity. }
      destruct (Rm.[vs.[k] * n + us.[k]] && Sint63.ltb (h1.[us.[k]] + ws.[k]) h1.[vs.[k]]) eqn:Ec.
      + split; [rewrite alen_set_b; exact L1|]. intros a Ha'.
        rewrite atb_set by (rewrite ?L1; unfold N in *; pose proof N_wB; lia).
        destruct (Z.eqb_spec a (φ (us.[k]))) as [-> | Hne].
        * split; [intros _; exists (φ k); split; [lia | split; [apply au_phi | apply Hv; reflexivity]] | auto].
        * rewrite L2 by exact Ha'. split.
          -- intros (j & Hj & E1 & E2). exists j. split; [lia | auto].
          -- intros (j & Hj & E1 & E2). exists j. split; [| auto].
             destruct (Z.eq_dec j (φ k)) as [-> | Hne2]; [rewrite au_phi in E1; congruence | lia].
      + split; [exact L1|]. intros a Ha'. rewrite L2 by exact Ha'. split.
        * intros (j & Hj & E1 & E2). exists j. split; [lia | auto].
        * intros (j & Hj & E1 & E2). exists j. split; [| auto].
          destruct (Z.eq_dec j (φ k)) as [-> | Hne2]; [| lia].
          apply Hv in E2. congruence.
  Qed.

  (* every negative closed walk passes through a bad vertex *)
  Lemma sum_or_viol : forall x y c L, pw Ge x y c L -> RG y x ->
    (exists a, In a L /\ atb bad a = true) \/ (sat h1 y - sat h1 x <= c)%Z.
  Proof.
    intros x y c L H. induction H as [| v v' w c L H IH He]; intros Hr; [right; lia|].
    assert (Hrv : RG v x) by (apply (R_trans Ge v v' x); [eapply R_edge; eauto | exact Hr]).
    destruct (IH Hrv) as [(a & Ha & Hb) | Hs]; [left; exists a; split; [right; exact Ha | exact Hb]|].
    destruct He as (k & Hk & Eu & Ev & Ew).
    destruct (Z_lt_le_dec (sat h1 v + w) (sat h1 v')) as [Hlt | Hge]; [| right; lia].
    left. exists v. split.
    - right. destruct (pw_head Ge x v c L H) as [L' ->]. left. reflexivity.
    - destruct bad_spec as [_ B]. destruct (Hend k Hk) as [Hu _].
      apply B; [lia|]. exists k. split; [exact Hk | split; [exact Eu|]].
      split; [| subst; lia]. subst v v'.
      apply (R_trans Ge (av k) x (au k)); [exact Hr | exists c, L; exact H].
  Qed.

  Lemma neg_has_bad : forall z c L, pw Ge z z c L -> (c < 0)%Z -> exists a, In a L /\ atb bad a = true.
  Proof.
    intros z c L H Hc. destruct (sum_or_viol z z c L H (R_refl Ge z)) as [E | E]; [exact E | lia].
  Qed.

  (* every bad vertex lies on a negative closed walk *)
  Lemma bad_neg : forall a, (0 <= a < N)%Z -> atb bad a = true ->
    exists c L, pw Ge a a c L /\ (c < 0)%Z.
  Proof.
    intros a Ha Hb. destruct bad_spec as [_ B]. apply B in Hb; [| exact Ha].
    destruct Hb as (k & Hk & Eu & Hrv & Hlt).
    destruct h1_spec as (_ & W & _ & O).
    destruct (Hend k Hk) as [Hu Hv].
    destruct (W (au k) Hu) as (x & c & L & Hw & Hc).
    assert (He : Gf P1 (au k) (av k) (aw k)) by (split; [exists k; auto | exact Hrv]).
    assert (Hw' : pw (Gf P1) x (av k) (c + aw k) (av k :: L)) by (econstructor; eauto).
    destruct (shorten (Gf P1) x (av k) _ _ Hw') as [(z & Hxz & Hzb & c1 & L1 & Hcl & Hneg) | (c' & L' & Hs & Hc' & Hnd)].
    - (* the negative closed walk at z is in the component of a *)
      assert (Hzb' : RG z (av k)) by (eapply R_mono; [apply Gf_Ge | exact Hzb]).
      assert (Hbz : RG (av k) z).
      { destruct Hzb as (c2 & L2 & H2). eapply (rev_reach (Gf P1)); [| exact H2].
        intros a0 b0 w0 [_ Hp]. exact Hp. }
      assert (Hab : RG a (av k)) by (rewrite <- Eu; eapply R_edge; exists k; eauto).
      apply pw_mono with (E' := Ge) in Hcl; [| apply Gf_Ge].
      destruct (neg_loop_short z a a c1 L1 Hcl Hneg (R_trans Ge a (av k) z Hab Hbz)
                  (R_trans Ge z (av k) a Hzb' ltac:(rewrite <- Eu; exact Hrv)) 0%Z) as (c2 & L2 & H2 & Hc2).
      exists c2, L2. split; [exact H2 | exact Hc2].
    - exfalso.
      assert (Hx : (0 <= x < N)%Z) by (eapply (pw_start (Gf P1) N (Gf_bounds P1)); [exact Hw | exact Hu]).
      pose proof (nodup_walk_len (Gf P1) (Gf_bounds P1) x (av k) c' L' Hs Hx Hnd) as Hl.
      pose proof (O (av k) x c' L' Hv Hs ltac:(lia)). lia.
  Qed.

  (* the potentials, over the edges between good vertices *)
  Definition keep2 (k : int) : bool := negb bad.[us.[k]] && negb bad.[vs.[k]].
  Definition P2 (a b : Z) : Prop := atb bad a = false /\ atb bad b = false.

  Lemma keep2_spec : forall k, (0 <= k < M)%Z -> (keep2 (of_Z k) = true <-> P2 (au k) (av k)).
  Proof.
    intros k Hk. unfold keep2, P2. rewrite andb_true_iff, !negb_true_iff.
    unfold au, av, at_, atb. rewrite !of_to_Z. reflexivity.
  Qed.

  Definition pot := bf n (PArray.length us) us vs ws keep2.

  Lemma G2_vertices : forall x y c L, pw (Gf P2) x y c L ->
    (L = [x] /\ c = 0%Z) \/ (forall a, In a L -> atb bad a = false).
  Proof.
    intros x y c L H. induction H as [| v v' w c L H IH He]; [left; auto|].
    right. destruct He as [_ [Pv Pv']]. intros a [<- | Ha]; [exact Pv'|].
    destruct IH as [[HL _] | IH]; [| apply IH; exact Ha].
    subst L. destruct (pw_head _ _ _ _ _ H) as [L' E]. injection E as Ev _.
    destruct Ha as [<- | []]. rewrite Ev. exact Pv.
  Qed.

  Lemma G2_no_neg : forall z c L, pw (Gf P2) z z c L -> (0 <= c)%Z.
  Proof.
    intros z c L H. destruct (Z_lt_le_dec c 0) as [Hc | Hc]; [| exact Hc]. exfalso.
    destruct (neg_has_bad z c L (pw_mono _ _ (Gf_Ge P2) _ _ _ _ H) Hc) as (a & Ha & Hb).
    destruct (G2_vertices z z c L H) as [[_ E] | Hg]; [lia|].
    rewrite (Hg a Ha) in Hb. discriminate.
  Qed.

  Lemma G2_shorten : forall x y c L, pw (Gf P2) x y c L -> (0 <= x < N)%Z ->
    exists c' L', pw (Gf P2) x y c' L' /\ (c' <= c)%Z /\ (Z.of_nat (List.length L') <= N)%Z.
  Proof.
    intros x y c L H Hx.
    destruct (shorten (Gf P2) x y c L H) as [(z & _ & _ & c1 & L1 & Hcl & Hneg) | (c' & L' & Hs & Hc & Hnd)].
    - pose proof (G2_no_neg z c1 L1 Hcl). lia.
    - exists c', L'. split; [exact Hs | split; [exact Hc|]].
      exact (nodup_walk_len (Gf P2) (Gf_bounds P2) x y c' L' Hs Hx Hnd).
  Qed.

  Lemma pot_spec : PArray.length pot = n /\
    (forall v x c L, (0 <= v < N)%Z -> pw (Gf P2) x v c L -> (sat pot v <= c)%Z) /\
    (forall v, (0 <= v < N)%Z -> exists x c L, pw (Gf P2) x v c L /\ c = sat pot v) /\
    (forall a b w, Gf P2 a b w -> (sat pot b <= sat pot a + w)%Z) /\
    (forall v, (0 <= v < N)%Z -> (- 1000 * (N - 1) <= sat pot v <= 0)%Z).
  Proof.
    destruct (bf_spec keep2 P2 keep2_spec) as (L1 & W & B & O). fold pot in L1, W, B, O.
    assert (Q1 : forall v x c L, (0 <= v < N)%Z -> pw (Gf P2) x v c L -> (sat pot v <= c)%Z).
    { intros v x c L Hv H.
      assert (Hx : (0 <= x < N)%Z) by (eapply (pw_start (Gf P2) N (Gf_bounds P2)); eauto).
      destruct (G2_shorten x v c L H Hx) as (c' & L' & Hs & Hc & Hl).
      pose proof (O v x c' L' Hv Hs ltac:(lia)). lia. }
    split; [exact L1 | split; [exact Q1 | split; [exact W | split]]].
    - intros a b w He. pose proof (Gf_bounds P2 a b w He) as [Ha Hb].
      destruct (W a Ha) as (x & c & L & H & Hc).
      pose proof (Q1 b x (c + w)%Z (b :: L) Hb ltac:(econstructor; eauto)). lia.
    - intros v Hv. split; [| pose proof (B v Hv); lia].
      destruct (W v Hv) as (x & c & L & H & Hc).
      assert (Hx : (0 <= x < N)%Z) by (eapply (pw_start (Gf P2) N (Gf_bounds P2)); eauto).
      destruct (G2_shorten x v c L H Hx) as (c' & L' & Hs & Hc' & Hl).
      pose proof (pw_cost (Gf P2) (-1000) 1000 ltac:(intros a b w0 He; eapply Ge_w; apply He) x v c' L' Hs).
      pose proof (pw_len_pos _ _ _ _ _ Hs). nia.
  Qed.
End Potentials.

(* ------------------------------------------------------------------ *)
(* Dijkstra                                                            *)
(* ------------------------------------------------------------------ *)

Fixpoint cntb (v : Z) (c : nat) : Z :=
  match c with
  | O => 0
  | S c' => (cntb v c' + if Z.eqb (au (Z.of_nat c')) v then 1 else 0)%Z
  end.

Fixpoint remc (dn : array bool) (c : nat) : Z :=
  match c with
  | O => 0
  | S c' => (remc dn c' + if atb dn (au (Z.of_nat c')) then 0 else 1)%Z
  end.

Definition cnt (v c : Z) : Z := cntb v (Z.to_nat c).
Definition Rem (dn : array bool) : Z := remc dn (Z.to_nat M).

Lemma cnt_succ : forall v c, (0 <= c)%Z -> cnt v (c + 1) = (cnt v c + if Z.eqb (au c) v then 1 else 0)%Z.
Proof.
  intros v c Hc. unfold cnt. rewrite Z2Nat.inj_add by lia. rewrite Nat.add_1_r. simpl.
  rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma cnt_nonneg : forall v c, (0 <= cnt v c)%Z.
Proof. intros v c. unfold cnt. induction (Z.to_nat c); simpl; [lia|]. destruct (Z.eqb _ _); lia. Qed.

Lemma cnt_flat : forall v c1 c2, (0 <= c1 <= c2)%Z ->
  (forall e, (c1 <= e < c2)%Z -> au e <> v) -> cnt v c2 = cnt v c1.
Proof.
  intros v c1 c2 [H1 H2]. pattern c2. apply Zlt_lower_bound_ind with (z := c1); [| lia].
  intros x IH Hx Hf. destruct (Z.eq_dec x c1) as [-> | Hne]; [reflexivity|].
  replace x with ((x - 1) + 1)%Z by lia. rewrite cnt_succ by lia.
  destruct (Z.eqb_spec (au (x - 1)) v) as [E | E]; [exfalso; apply (Hf (x - 1)%Z); [lia | exact E]|].
  rewrite Z.add_0_r. apply IH; [lia | intros e He; apply Hf; lia].
Qed.

Lemma cnt_Lb : forall v c e, (0 <= e)%Z -> (e < c)%Z -> Lb v c = (e + 1)%Z -> cnt v c = (cnt v e + 1)%Z.
Proof.
  intros v c e He Hec HL. destruct (Lb_props v c ltac:(lia)) as (_ & L2 & _).
  destruct (L2 e HL He) as (A1 & _ & A3).
  rewrite (cnt_flat v (e + 1) c) by (try lia; intros e' He'; apply A3; lia).
  rewrite cnt_succ by lia. rewrite A1, Z.eqb_refl. reflexivity.
Qed.

Lemma cnt_Lb0 : forall v c, (0 <= c)%Z -> Lb v c = 0%Z -> cnt v c = 0%Z.
Proof.
  intros v c Hc HL. destruct (Lb_props v c Hc) as (_ & _ & L3).
  rewrite (cnt_flat v 0 c) by (try lia; intros e He; apply (L3 HL); lia). reflexivity.
Qed.

Lemma remc_set : forall dn (v : int) c, (0 <= (φ v) < N)%Z -> PArray.length dn = n ->
  atb dn (φ v) = false -> (c <= Z.to_nat M)%nat ->
  remc (dn.[v <- true]) c = (remc dn c - cntb (φ v) c)%Z.
Proof.
  intros dn v c Hv Hl Hd. induction c as [| c IH]; intros Hc; simpl; [reflexivity|].
  rewrite IH by lia.
  destruct (Hend (Z.of_nat c) ltac:(lia)) as [Hu _].
  rewrite atb_set by (rewrite ?Hl; unfold N in *; pose proof N_wB; lia).
  destruct (Z.eqb_spec (au (Z.of_nat c)) (φ v)) as [E | E].
  - rewrite E, Hd. lia.
  - destruct (atb dn (au (Z.of_nat c))); lia.
Qed.

Lemma remc_ge_cnt : forall dn v c, atb dn v = false -> (cntb v c <= remc dn c)%Z.
Proof.
  intros dn v c Hd. induction c as [| c IH]; simpl; [lia|].
  destruct (Z.eqb_spec (au (Z.of_nat c)) v) as [E | E].
  - rewrite E, Hd. lia.
  - destruct (atb dn (au (Z.of_nat c))); lia.
Qed.

Lemma remc_bound : forall dn c, (0 <= remc dn c <= Z.of_nat c)%Z.
Proof. intros dn c. induction c as [| c IH]; simpl; [lia|]. destruct (atb dn _); lia. Qed.

Lemma remc_all : forall c, remc (PArray.make n false) c = Z.of_nat c.
Proof. intros c. induction c as [| c IH]; simpl; [reflexivity|]. rewrite atb_make, IH. lia. Qed.

Section Dij.
  Variables (hd nx : array int).
  Hypothesis Hhd : forall a, (0 <= a < N)%Z -> at_ hd a = Lb a M.
  Hypothesis Hnx : forall e, (0 <= e < M)%Z -> at_ nx e = Lb (au e) e.
  Variables (bd : array bool) (p : array int).
  Hypothesis Hlb : PArray.length bd = n.
  Hypothesis Hlp : PArray.length p = n.

  Definition Pg (a b : Z) : Prop := atb bd a = false /\ atb bd b = false.
  Definition Gs := Gf Pg.

  Hypothesis Hfeas : forall a b w, Gs a b w -> (sat p b <= sat p a + w)%Z.
  Hypothesis Hpb : forall v, (0 <= v < N)%Z -> (- 1000 * (N - 1) <= sat p v <= 0)%Z.
  Hypothesis Hshort : forall x y c L, pw Gs x y c L -> (0 <= x < N)%Z ->
    exists c' L', pw Gs x y c' L' /\ (c' <= c)%Z /\ (Z.of_nat (List.length L') <= N)%Z.

  Definition Erw (a b w' : Z) : Prop := exists w, Gs a b w /\ w' = (w + sat p a - sat p b)%Z.

  Lemma Erw_bounds : forall a b w', Erw a b w' -> (0 <= a < N /\ 0 <= b < N)%Z.
  Proof. intros a b w' (w & H & _). eapply Gf_bounds; eauto. Qed.

  Lemma Erw_w : forall a b w', Erw a b w' -> (0 <= w' <= 1000 * N)%Z.
  Proof.
    intros a b w' (w & H & ->). pose proof (Hfeas a b w H).
    destruct (Gf_bounds Pg a b w H) as [Ha Hb]. pose proof (Hpb a Ha). pose proof (Hpb b Hb).
    pose proof (Ge_w a b w (Gf_Ge Pg a b w H)). lia.
  Qed.

  Lemma rw_of : forall x y c L, pw Gs x y c L -> pw Erw x y (c + sat p x - sat p y) L.
  Proof.
    intros x y c L H. induction H as [| v v' w c L H IH He].
    - replace (0 + sat p x - sat p x)%Z with 0%Z by lia. constructor.
    - replace (c + w + sat p x - sat p v')%Z with ((c + sat p x - sat p v) + (w + sat p v - sat p v'))%Z by lia.
      econstructor; [exact IH | exists w; auto].
  Qed.

  Lemma of_rw : forall x y c L, pw Erw x y c L -> exists c0, pw Gs x y c0 L /\ c = (c0 + sat p x - sat p y)%Z.
  Proof.
    intros x y c L H. induction H as [| v v' w' c L H IH He].
    - exists 0%Z. split; [constructor | lia].
    - destruct IH as (c0 & H0 & E). destruct He as (w & Hw & Ew).
      exists (c0 + w)%Z. split; [econstructor; eauto | lia].
  Qed.

  Lemma rw_short : forall x y c L, pw Erw x y c L -> (0 <= x < N)%Z ->
    exists c' L', pw Erw x y c' L' /\ (c' <= 2000 * N)%Z.
  Proof.
    intros x y c L H Hx. destruct (of_rw x y c L H) as (c0 & H0 & E).
    destruct (Hshort x y c0 L H0 Hx) as (c' & L' & Hs & Hc & Hl).
    exists (c' + sat p x - sat p y)%Z, L'. split; [apply rw_of; exact Hs|].
    pose proof (pw_cost Gs (-1000) 1000 ltac:(intros a b w0 He; eapply Ge_w; apply (Gf_Ge _ _ _ _ He)) x y c' L' Hs).
    pose proof (pw_len_pos _ _ _ _ _ Hs).
    assert (Hy : (0 <= y < N)%Z).
    { destruct (pw_head _ _ _ _ _ Hs) as [L'' E']. 
      apply (pw_vertices Gs N (Gf_bounds Pg) x y c' L' Hs Hx). rewrite E'. left. reflexivity. }
    pose proof (Hpb x Hx). pose proof (Hpb y Hy). nia.
  Qed.

  Lemma Erw_nonneg : forall x y c L, pw Erw x y c L -> (0 <= c)%Z.
  Proof.
    intros x y c L H. induction H; [lia|]. pose proof (Erw_w _ _ _ H0). lia.
  Qed.

  Definition sound (U : Z) (hp : array int) (sz : Z) : Prop :=
    forall j, (0 <= j < sz)%Z ->
      (0 <= at_ hp j mod 256 < N)%Z /\ exists L, pw Erw U (at_ hp j mod 256) (at_ hp j / 256) L.

  Definition rinv (U : Z) (dn' : array bool) (v d : int)
      (D0 hp0 : array int) (sz0 : int) (c : Z) (st : array int * array int * int) : Prop :=
    let '(D2, hp2, sz2) := st in
    PArray.length D2 = n /\ PArray.length hp2 = PArray.length hp0 /\ heap_ok hp2 (φ sz2) /\
    sound U hp2 (φ sz2) /\
    (forall j, (0 <= j < (φ sz0))%Z -> exists j', (0 <= j' < (φ sz2))%Z /\ at_ hp2 j' = at_ hp0 j) /\
    (forall y, (0 <= y < N)%Z -> (at_ D2 y <= at_ D0 y)%Z /\ (atb dn' y = true -> at_ D2 y = at_ D0 y)) /\
    (forall y, (0 <= y < N)%Z -> atb dn' y = false -> at_ D2 y <> at_ D0 y ->
       exists j', (0 <= j' < (φ sz2))%Z /\ at_ hp2 j' = (at_ D2 y * 256 + y)%Z) /\
    (forall e, (c <= e < M)%Z -> au e = (φ v) -> Pg (φ v) (av e) -> atb dn' (av e) = false ->
       (at_ D2 (av e) <= (φ d) + (aw e + sat p (φ v) - sat p (av e)))%Z) /\
    ((φ sz2) + cnt (φ v) c <= (φ sz0) + cnt (φ v) M)%Z.

  Lemma relax_chain : forall (U : Z) (dn' : array bool) (v d : int) D0 hp0 sz0,
    PArray.length dn' = n -> (0 <= (φ v) < N)%Z -> atb dn' (φ v) = true -> atb bd (φ v) = false ->
    (exists L, pw Erw U (φ v) (φ d) L) -> ((φ d) <= 2000 * N)%Z ->
    PArray.length D0 = n -> PArray.length hp0 = PArray.length us + 1 ->
    heap_ok hp0 (φ sz0) -> sound U hp0 (φ sz0) ->
    ((φ sz0) + cnt (φ v) M <= M)%Z ->
    let st := chain_fold nx (relax vs ws bd dn' p v d) hd.[v] (D0, hp0, sz0) in
    exists c, (0 <= c <= M)%Z /\ Lb (φ v) c = 0%Z /\ rinv U dn' v d D0 hp0 sz0 c st.
  Proof.
    intros U dn' v d D0 hp0 sz0 Hldn Hv Hvd Hvb Hwd Hdb HlD Hlh Hh0 Hs0 Hcnt. cbv zeta.
    pose proof N_wB as HNw. pose proof M_nonneg as HM0.
    assert (HlhZ : (φ (PArray.length hp0)) = (M + 1)%Z).
    { rewrite Hlh. apply phi_add1. pose proof (alen_bound_i us). unfold M in *. clear - H. lia. }
    pose proof (cnt_nonneg (φ v) M).
    refine (chain_spec nx _ (φ v) (rinv U dn' v d D0 hp0 sz0) Hnx _ (hd.[v]) M (D0, hp0, sz0) _ _ _);
      [ | clear - HM0; lia | | ].
    3: { split; [exact HlD | split; [reflexivity | split; [exact Hh0 | split; [exact Hs0 | split]]]].
         - intros j Hj. exists j. auto.
         - split; [intros y Hy; lia | split; [intros y Hy _ E; congruence | split; [intros e He; lia | lia]]]. }
    2: { rewrite <- (Hhd (φ v) Hv), at_phi. reflexivity. }
    intros c e [[D2 hp2] sz2] He Hc HL (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
    destruct (Lb_props (φ v) c ltac:(lia)) as (_ & L2 & _).
    destruct (L2 e HL ltac:(lia)) as (A1 & A2 & A3).
    assert (Hcnt' := cnt_Lb (φ v) c e ltac:(lia) A2 HL). pose proof (cnt_nonneg (φ v) e).
    destruct (Hend e ltac:(lia)) as [_ Hb]. pose proof (Hwt e ltac:(lia)) as Hw.
    assert (Eb : (φ (vs.[of_Z e])) = av e) by reflexivity.
    assert (Ew : Sint63.to_Z (ws.[of_Z e]) = aw e) by reflexivity.
    (* C8 for the edges above e is inherited *)
    assert (R8' : forall D3, (forall y, (0 <= y < N)%Z -> (at_ D3 y <= at_ D2 y)%Z) ->
      forall e', (e + 1 <= e' < M)%Z -> au e' = (φ v) -> Pg (φ v) (av e') -> atb dn' (av e') = false ->
       (at_ D3 (av e') <= (φ d) + (aw e' + sat p (φ v) - sat p (av e')))%Z).
    { intros D3 HD3 e' He' Hu' Hp' Hd'. destruct (Z_lt_le_dec e' c) as [Hlt | Hge].
      - exfalso. apply (A3 e'); [lia | exact Hu'].
      - destruct (Hend e' ltac:(lia)) as [_ Hb']. pose proof (HD3 _ Hb').
        pose proof (R8 e' ltac:(lia) Hu' Hp' Hd'). lia. }
    unfold relax.
    destruct (negb bd.[vs.[of_Z e]] && negb dn'.[vs.[of_Z e]]) eqn:Eg.
    - apply andb_true_iff in Eg. destruct Eg as [Eg1 Eg2]. rewrite negb_true_iff in Eg1, Eg2.
      rewrite <- atb_phi, Eb in Eg1, Eg2.
      assert (HG : Gs (φ v) (av e) (aw e)) by (split; [exists e; split; [lia | auto] | split; [exact Hvb | exact Eg1]]).
      pose proof (Hfeas _ _ _ HG) as Hf.
      pose proof (Hpb _ Hv) as Hpv. pose proof (Hpb _ Hb) as Hpbb.
      assert (Ed : Sint63.to_Z d = (φ d)) by (apply s_of_u; lia).
      assert (Pv : Sint63.to_Z (p.[v]) = sat p (φ v)) by (rewrite sat_phi; reflexivity).
      assert (Pb : Sint63.to_Z (p.[vs.[of_Z e]]) = sat p (av e)) by (rewrite <- Eb, sat_phi; reflexivity).
      set (nd := d + ws.[of_Z e] + p.[v] - p.[vs.[of_Z e]]).
      assert (End : Sint63.to_Z nd = ((φ d) + aw e + sat p (φ v) - sat p (av e))%Z).
      { unfold nd. rewrite s_sub; rewrite ?s_add; rewrite ?Ed, ?Ew, ?Pv, ?Pb; try lia;
        rewrite ?s_add; rewrite ?Ed, ?Ew; lia. }
      assert (Endu : (φ nd) = ((φ d) + aw e + sat p (φ v) - sat p (av e))%Z) by (rewrite u_of_s; lia).
      destruct (nd <? D2.[vs.[of_Z e]]) eqn:Elt.
      + rewrite ltb_spec in Elt. rewrite <- (at_phi D2), Eb in Elt.
        assert (Hsz : ((φ sz2) < (φ (PArray.length hp2)))%Z) by (rewrite R2, HlhZ; lia).
        destruct (hpush_spec hp2 sz2 (nd * 256 + vs.[of_Z e]) R3 Hsz) as (P1 & P2 & P3 & P4 & P5).
        assert (Es : (φ (sz2 + 1)) = ((φ sz2) + 1)%Z) by (apply phi_add1; lia).
        assert (Ek : (φ (nd * 256 + vs.[of_Z e])) = ((φ nd) * 256 + av e)%Z).
        { rewrite add_spec, mul_spec, Eb. change (φ 256) with 256%Z.
          rewrite (Z.mod_small ((φ nd) * 256)) by (rewrite wB_val; lia).
          apply Z.mod_small. rewrite wB_val. lia. }
        assert (Kmod : (((φ nd) * 256 + av e) mod 256 = av e)%Z) by (rewrite Z.add_comm, Z_mod_plus_full; apply Z.mod_small; lia).
        assert (Kdiv : (((φ nd) * 256 + av e) / 256 = (φ nd))%Z) by (rewrite Z.add_comm, Z_div_plus_full by lia; rewrite Z.div_small by lia; lia).
        assert (AD : forall y, (0 <= y < N)%Z -> at_ D2.[vs.[of_Z e] <- nd] y = if Z.eqb y (av e) then (φ nd) else at_ D2 y)
          by (intros y Hy; rewrite at_set by (rewrite ?R1; unfold N in *; lia); rewrite Eb; reflexivity).
        unfold rinv. rewrite Es.
        split; [rewrite alen_set_i; exact R1 | split; [rewrite P2; exact R2 | split; [exact P1 | split]]].
        * intros j' Hj'. destruct (P5 j' Hj') as [Ex | (j & Hj & Ex)].
          -- rewrite Ex, Ek, Kmod, Kdiv. split; [lia|].
             destruct Hwd as [Lv Hpv']. exists (av e :: Lv).
             replace (φ nd) with ((φ d) + (aw e + sat p (φ v) - sat p (av e)))%Z by lia.
             econstructor; [exact Hpv' | exists (aw e); split; [exact HG | reflexivity]].
          -- rewrite Ex. apply R4. exact Hj.
        * split; [| split; [| split; [| split]]].
          -- intros j Hj. destruct (R5 j Hj) as (j1 & Hj1 & E1). destruct (P3 j1 Hj1) as (j2 & Hj2 & E2).
             exists j2. split; [exact Hj2 | congruence].
          -- intros y Hy. rewrite AD by exact Hy. destruct (R6 y Hy) as [R6a R6b].
             destruct (Z.eqb_spec y (av e)) as [-> | Hne].
             ++ split; [lia | intros E; congruence].
             ++ split; [exact R6a | exact R6b].
          -- intros y Hy Hdy Hne. rewrite AD by exact Hy. rewrite AD in Hne by exact Hy.
             destruct (Z.eqb_spec y (av e)) as [-> | Hne2].
             ++ destruct P4 as (j' & Hj' & Ej'). exists j'. split; [exact Hj'|]. rewrite Ej', Ek. reflexivity.
             ++ destruct (R7 y Hy Hdy Hne) as (j1 & Hj1 & E1). destruct (P3 j1 Hj1) as (j2 & Hj2 & E2).
                exists j2. split; [lia | congruence].
          -- intros e' He' Hu' Hp' Hd'. destruct (Z.eq_dec e' e) as [-> | Hne].
             ++ rewrite AD by exact Hb. rewrite Z.eqb_refl. lia.
             ++ apply (R8' D2.[vs.[of_Z e] <- nd]); [| lia | exact Hu' | exact Hp' | exact Hd'].
                intros y Hy. rewrite AD by exact Hy. destruct (Z.eqb_spec y (av e)) as [-> | _]; lia.
          -- lia.
      + rewrite <- Bool.not_true_iff_false, ltb_spec in Elt. rewrite <- (at_phi D2), Eb in Elt.
        split; [exact R1 | split; [exact R2 | split; [exact R3 | split; [exact R4 | split; [exact R5 | split; [exact R6 | split; [exact R7 | split]]]]]]].
        * intros e' He' Hu' Hp' Hd'. destruct (Z.eq_dec e' e) as [-> | Hne]; [lia|].
          apply (R8' D2); [intros; lia | lia | exact Hu' | exact Hp' | exact Hd'].
        * lia.
    - split; [exact R1 | split; [exact R2 | split; [exact R3 | split; [exact R4 | split; [exact R5 | split; [exact R6 | split; [exact R7 | split]]]]]]].
      + intros e' He' Hu' [Hp1 Hp2] Hd'. destruct (Z.eq_dec e' e) as [-> | Hne].
        * exfalso. rewrite <- Eb, !atb_phi in *. rewrite Hp2, Hd' in Eg. discriminate.
        * apply (R8' D2); [intros; lia | lia | exact Hu' | split; auto | exact Hd'].
      + lia.
  Qed.

  Lemma key_mod : forall x y, (0 <= y < 256)%Z -> ((x * 256 + y) mod 256 = y)%Z.
  Proof. intros x y Hy. rewrite Z.add_comm, Z_mod_plus_full. apply Z.mod_small. lia. Qed.

  Lemma key_div : forall x y, (0 <= y < 256)%Z -> ((x * 256 + y) / 256 = x)%Z.
  Proof. intros x y Hy. rewrite Z.add_comm, Z_div_plus_full by lia. rewrite Z.div_small by lia. lia. Qed.

  Lemma INF_val : (φ INF) = 1073741824%Z.
  Proof. reflexivity. Qed.

  Record dinv (U : Z) (D : array int) (dn : array bool) (hp : array int) (sz steps : int) : Prop := {
    di_lD : PArray.length D = n;
    di_ldn : PArray.length dn = n;
    di_lhp : PArray.length hp = PArray.length us + 1;
    di_heap : heap_ok hp (φ sz);
    di_sound : sound U hp (φ sz);
    di_done : forall y, (0 <= y < N)%Z -> atb dn y = true ->
       (exists L, pw Erw U y (at_ D y) L) /\ (forall c L, pw Erw U y c L -> (at_ D y <= c)%Z);
    di_tent : forall y, (0 <= y < N)%Z -> atb dn y = false -> at_ D y <> (φ INF) ->
       exists j, (0 <= j < (φ sz))%Z /\ at_ hp j = (at_ D y * 256 + y)%Z;
    di_front : forall a b w, Erw a b w -> atb dn a = true -> atb dn b = false ->
       (at_ D b <= at_ D a + w)%Z;
    di_src : atb dn U = false -> at_ D U = 0%Z;
    di_count : ((φ steps) + (φ sz) + Rem dn <= M + 1)%Z
  }.

  Lemma done_bound : forall U D dn hp sz steps, (0 <= U < N)%Z -> dinv U D dn hp sz steps ->
    forall y, (0 <= y < N)%Z -> atb dn y = true -> (at_ D y <= 2000 * N)%Z.
  Proof.
    intros U D dn hp sz steps HU DI y Hy Hd. destruct (di_done _ _ _ _ _ _ DI y Hy Hd) as [[L HW] Ho].
    destruct (rw_short U y _ L HW HU) as (c' & L' & Hs & Hc). pose proof (Ho c' L' Hs). lia.
  Qed.

  Lemma frontier : forall U D dn hp sz steps, (0 <= U < N)%Z -> dinv U D dn hp sz steps ->
    forall y c L, pw Erw U y c L ->
    (atb dn y = true /\ (at_ D y <= c)%Z) \/ (exists j, (0 <= j < (φ sz))%Z /\ (at_ hp j / 256 <= c)%Z).
  Proof.
    intros U D dn hp sz steps HU DI y c L H.
    pose proof INF_val as HI.
    induction H as [| a b w c L H IH He].
    - destruct (atb dn U) eqn:Ed.
      + left. split; [reflexivity|]. apply (proj2 (di_done _ _ _ _ _ _ DI U HU Ed) 0%Z [U]). constructor.
      + right. pose proof (di_src _ _ _ _ _ _ DI Ed) as E0.
        destruct (di_tent _ _ _ _ _ _ DI U HU Ed ltac:(lia)) as (j & Hj & Ej).
        exists j. split; [exact Hj|]. rewrite Ej, E0, key_div by lia. lia.
    - pose proof (Erw_w _ _ _ He) as Hw. destruct (Erw_bounds _ _ _ He) as [Ha Hb].
      destruct IH as [[Hda Hca] | (j & Hj & Ej)]; [| right; exists j; split; [exact Hj | lia]].
      destruct (atb dn b) eqn:Edb.
      + left. split; [reflexivity|]. apply (proj2 (di_done _ _ _ _ _ _ DI b Hb Edb) (c + w)%Z (b :: L)).
        econstructor; eauto.
      + right. pose proof (di_front _ _ _ _ _ _ DI a b w He Hda Edb) as Hf.
        pose proof (done_bound _ _ _ _ _ _ HU DI a Ha Hda) as Hba.
        destruct (di_tent _ _ _ _ _ _ DI b Hb Edb ltac:(lia)) as (j & Hj & Ej).
        exists j. split; [exact Hj|]. rewrite Ej, key_div by lia. lia.
  Qed.

  Lemma dij_step : forall U D dn hp sz steps, (0 <= U < N)%Z ->
    dinv U D dn hp sz steps -> (0 < (φ sz))%Z -> ((φ steps) < M + 1)%Z ->
    let '(D2, dn2, hp2, sz2) := dij_body hd nx vs ws bd p (D, dn, hp, sz) in
    dinv U D2 dn2 hp2 sz2 (steps + 1).
  Proof.
    intros U D dn hp sz steps HU DI Hsz Hst.
    pose proof INF_val as HI. pose proof N_wB as HNw. pose proof M_nonneg as HM0.
    pose proof DI as DI0.
    destruct DI as [L1 L2 L3 Hh Hs Hd Ht Hf Hsrc Hc].
    assert (HlhZ : (φ (PArray.length hp)) = (M + 1)%Z).
    { rewrite L3. apply phi_add1. pose proof (alen_bound_i us) as H. unfold M in *. clear - H. lia. }
    assert (HR0 : (0 <= Rem dn)%Z) by (unfold Rem; apply remc_bound). pose proof (to_Z_bounded steps) as Bst.
    destruct (hpop_spec hp sz Hh Hsz ltac:(lia)) as (P1 & P2 & P3 & P4 & P5 & P6).
    unfold dij_body. destruct (hpop hp sz) as [top hp1] eqn:Ep. simpl in P1, P3, P4, P5, P6.
    assert (Hst1 : (φ (steps + 1)) = ((φ steps) + 1)%Z) by (apply phi_add1; lia).
    assert (Hsz1 : (φ (sz - 1)) = ((φ sz) - 1)%Z).
    { rewrite sub_spec. change (φ 1) with 1%Z. apply Z.mod_small. pose proof (to_Z_bounded sz). lia. }
    assert (Etop : (φ top) = at_ hp 0) by (rewrite P1; reflexivity).
    destruct (Hs 0%Z ltac:(lia)) as [Hv0 [Lw Hw0]]. rewrite <- Etop in Hv0, Hw0.
    set (v := top mod 256). set (d := top / 256).
    assert (Ev : (φ v) = ((φ top) mod 256)%Z) by (unfold v; rewrite mod_spec; reflexivity).
    assert (Edd : (φ d) = ((φ top) / 256)%Z) by (unfold d; rewrite div_spec; reflexivity).
    rewrite <- Ev in Hv0. rewrite <- Ev, <- Edd in Hw0.
    assert (Hsurv : forall y j, (0 <= j < (φ sz))%Z -> (at_ hp j mod 256)%Z = y -> y <> (φ v) ->
              exists j', (0 <= j' < (φ (sz - 1)))%Z /\ at_ hp1 j' = at_ hp j).
    { intros y j Hj Ey Hne. rewrite Hsz1. destruct (Z.eq_dec j 0) as [-> | Hj0].
      - exfalso. apply Hne. rewrite <- Ey, <- Etop, Ev. reflexivity.
      - apply P6. lia. }
    assert (Hs1 : sound U hp1 (φ (sz - 1))).
    { intros j Hj. rewrite Hsz1 in Hj. destruct (P5 j Hj) as (j0 & Hj0 & E). rewrite E. apply Hs. exact Hj0. }
    destruct (dn.[v]) eqn:Edv.
    - (* a stale entry *)
      cbv beta iota zeta.
      assert (Hdv : atb dn (φ v) = true) by (rewrite atb_phi; exact Edv).
      constructor; try assumption.
      + rewrite P4. exact L3.
      + rewrite Hsz1. exact P3.
      + intros y Hy Hdy Hne. destruct (Ht y Hy Hdy Hne) as (j & Hj & Ej).
        destruct (Hsurv y j Hj ltac:(rewrite Ej, key_mod by lia; reflexivity) ltac:(intro E; subst y; congruence))
          as (j' & Hj' & E'). exists j'. split; [exact Hj' | congruence].
      + rewrite Hst1, Hsz1. lia.
    - (* v is final *)
      assert (Hdv : atb dn (φ v) = false) by (rewrite atb_phi; exact Edv).
      assert (HB : forall c L, pw Erw U (φ v) c L -> ((φ d) <= c)%Z).
      { intros c L H. destruct (frontier U D dn hp sz steps HU DI0 (φ v) c L H) as [[E _] | (j & Hj & Ej)];
          [congruence|].
        pose proof (P2 j Hj) as Hm. rewrite <- P1 in Hm.
        rewrite Edd. pose proof (Z.div_le_mono _ _ 256 ltac:(lia) Hm). lia. }
      assert (Hdb : ((φ d) <= 2000 * N)%Z).
      { destruct (rw_short U (φ v) _ Lw Hw0 HU) as (c' & L' & Hs' & Hc'). pose proof (HB c' L' Hs'). lia. }
      assert (ADN : forall y, (0 <= y < N)%Z ->
                 atb dn.[v <- true] y = if Z.eqb y (φ v) then true else atb dn y)
        by (intros y Hy; apply atb_set; [rewrite L2; unfold N in *; lia | lia]).
      assert (AD : forall y, (0 <= y < N)%Z -> at_ D.[v <- d] y = if Z.eqb y (φ v) then (φ d) else at_ D y)
        by (intros y Hy; apply at_set; [rewrite L1; unfold N in *; lia | lia]).
      assert (ERem : Rem dn.[v <- true] = (Rem dn - cnt (φ v) M)%Z).
      { unfold Rem, cnt. apply remc_set; [lia | exact L2 | exact Hdv | lia]. }
      assert (Hge : (cnt (φ v) M <= Rem dn)%Z) by (unfold Rem, cnt; apply remc_ge_cnt; exact Hdv).
      pose proof (cnt_nonneg (φ v) M) as Hcn0.
      assert (HdnL : PArray.length dn.[v <- true] = n) by (rewrite alen_set_b; exact L2).
      assert (HDL : PArray.length D.[v <- d] = n) by (rewrite alen_set_i; exact L1).
      assert (Hdone_v : (exists L, pw Erw U (φ v) (at_ D.[v <- d] (φ v)) L) /\
                        (forall c L, pw Erw U (φ v) c L -> (at_ D.[v <- d] (φ v) <= c)%Z)).
      { rewrite AD, Z.eqb_refl by lia. split; [exists Lw; exact Hw0 | exact HB]. }
      cbv beta iota zeta.
      destruct (bd.[v]) eqn:Ebv.
      + (* a bad vertex: no edge of the reweighted graph leaves it *)
        constructor; try assumption.
        * rewrite P4. exact L3.
        * rewrite Hsz1. exact P3.
        * intros y Hy Hdy. rewrite ADN in Hdy by exact Hy.
          destruct (Z.eqb_spec y (φ v)) as [-> | Hne]; [exact Hdone_v|].
          rewrite AD by exact Hy. destruct (Z.eqb_spec y (φ v)); [congruence|]. apply Hd; auto.
        * intros y Hy Hdy Hne. rewrite ADN in Hdy by exact Hy. rewrite AD in Hne |- * by exact Hy.
          destruct (Z.eqb_spec y (φ v)) as [-> | Hne2]; [discriminate|].
          destruct (Ht y Hy Hdy Hne) as (j & Hj & Ej).
          destruct (Hsurv y j Hj ltac:(rewrite Ej, key_mod by lia; reflexivity) Hne2) as (j' & Hj' & E').
          exists j'. split; [exact Hj' | congruence].
        * intros a b w He Hda Hdb'. destruct (Erw_bounds _ _ _ He) as [Ha Hb].
          rewrite ADN in Hda, Hdb' by assumption. rewrite !AD by assumption.
          destruct (Z.eqb_spec a (φ v)) as [-> | Hna].
          -- exfalso. destruct He as (w0 & [_ [Pa _]] & _). rewrite atb_phi in Pa. congruence.
          -- destruct (Z.eqb_spec b (φ v)); [discriminate|]. apply Hf; auto.
        * intros Hdu. rewrite ADN in Hdu by exact HU. rewrite AD by exact HU.
          destruct (Z.eqb_spec U (φ v)); [discriminate|]. apply Hsrc. exact Hdu.
        * rewrite Hst1, Hsz1, ERem. lia.
      + (* relax the edges leaving v *)
        assert (Hbv : atb bd (φ v) = false) by (rewrite atb_phi; exact Ebv).
        pose proof (relax_chain U dn.[v <- true] v d D.[v <- d] hp1 (sz - 1) HdnL Hv0
                      ltac:(rewrite ADN, Z.eqb_refl by lia; reflexivity) Hbv (ex_intro _ Lw Hw0) Hdb HDL
                      ltac:(rewrite P4; exact L3) ltac:(rewrite Hsz1; exact P3) Hs1
                      ltac:(rewrite Hsz1; lia)) as RC.
        cbv zeta in RC.
        destruct (chain_fold nx (relax vs ws bd dn.[v <- true] p v d) hd.[v] (D.[v <- d], hp1, sz - 1))
          as [[D2 hp2] sz2].
        destruct RC as (c & Hc0 & HL0 & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
        pose proof (cnt_Lb0 (φ v) c ltac:(lia) HL0) as Hc00.
        destruct (Lb_props (φ v) c ltac:(lia)) as (_ & _ & LB3).
        constructor; try assumption.
        * rewrite R2, P4. exact L3.
        * intros y Hy Hdy. destruct (R6 y Hy) as [_ R6b]. rewrite (R6b Hdy).
          rewrite ADN in Hdy by exact Hy.
          destruct (Z.eqb_spec y (φ v)) as [-> | Hne]; [exact Hdone_v|].
          rewrite AD by exact Hy. destruct (Z.eqb_spec y (φ v)); [congruence|]. apply Hd; auto.
        * intros y Hy Hdy Hne. destruct (Z.eq_dec (at_ D2 y) (at_ D.[v <- d] y)) as [Eq | Neq];
            [| exact (R7 y Hy Hdy Neq)].
          rewrite ADN in Hdy by exact Hy. rewrite Eq in Hne |- *. rewrite AD in Hne |- * by exact Hy.
          destruct (Z.eqb_spec y (φ v)) as [-> | Hne2]; [discriminate|].
          destruct (Ht y Hy Hdy Hne) as (j & Hj & Ej).
          destruct (Hsurv y j Hj ltac:(rewrite Ej, key_mod by lia; reflexivity) Hne2) as (j' & Hj' & E').
          destruct (R5 j' Hj') as (j'' & Hj'' & E''). exists j''. split; [exact Hj'' | congruence].
        * intros a b w He Hda Hdb'. destruct (Erw_bounds _ _ _ He) as [Ha Hb].
          destruct (R6 a Ha) as [_ R6a]. rewrite (R6a Hda).
          destruct (R6 b Hb) as [R6b _].
          pose proof Hda as Hda'. pose proof Hdb' as Hdb''.
          rewrite ADN in Hda', Hdb'' by assumption.
          destruct (Z.eqb_spec a (φ v)) as [-> | Hna].
          -- destruct He as (w0 & [(k & Hk & Eu & Evk & Ew) HP] & ->).
             assert (Hck : (c <= k)%Z).
             { destruct (Z_lt_le_dec k c) as [Hlt | Hle]; [| exact Hle].
               exfalso. apply (LB3 HL0 k); [lia | exact Eu]. }
             pose proof (R8 k ltac:(lia) Eu ltac:(rewrite Evk; exact HP) ltac:(rewrite Evk; exact Hdb')) as Hr.
             rewrite Evk, Ew in Hr. rewrite AD, Z.eqb_refl by lia. exact Hr.
          -- destruct (Z.eqb_spec b (φ v)); [discriminate|].
             pose proof (Hf a b w He Hda' Hdb'') as Hfab.
             assert (E1 : at_ D.[v <- d] b = at_ D b)
               by (rewrite (AD b Hb); destruct (Z.eqb_spec b (φ v)); [congruence | reflexivity]).
             assert (E2 : at_ D.[v <- d] a = at_ D a)
               by (rewrite (AD a Ha); destruct (Z.eqb_spec a (φ v)); [congruence | reflexivity]).
             rewrite E2. rewrite E1 in R6b. clear - R6b Hfab. lia.
        * intros Hdu. destruct (R6 U HU) as [R6u _]. pose proof Hdu as Hdu'.
          rewrite ADN in Hdu' by exact HU. rewrite AD in R6u by exact HU.
          destruct (Z.eqb_spec U (φ v)); [discriminate|]. rewrite (Hsrc Hdu') in R6u.
          pose proof (to_Z_bounded (D2.[of_Z U])) as BD. unfold at_ in *. clear - BD R6u. lia.
        * rewrite Hst1, ERem. rewrite Hsz1 in R9. lia.
  Qed.

  Lemma lim_phi : (φ (PArray.length us + 1)) = (M + 1)%Z.
  Proof. apply phi_add1. pose proof (alen_bound_i us) as H. unfold M in *. clear - H. lia. Qed.

  Lemma dij_loop : forall U, (0 <= U < N)%Z -> forall z steps st H,
    gap (PArray.length us + 1) steps = z ->
    (let '(D, dn, hp, sz) := st in dinv U D dn hp sz steps) ->
    let Dr := dij_acc hd nx vs ws bd p (PArray.length us + 1) steps st H in
    PArray.length Dr = n /\
    forall y c L, (0 <= y < N)%Z -> pw Erw U y c L ->
      (exists L', pw Erw U y (at_ Dr y) L') /\ (forall c' L', pw Erw U y c' L' -> (at_ Dr y <= c')%Z).
  Proof.
    intros U HU z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros steps [[[D dn] hp] sz] H Hz DI. cbv zeta. rewrite dij_acc_eq.
    pose proof lim_phi as HL.
    destruct (bdec ((0 <? sz) && (steps <? PArray.length us + 1))) as [Hc | Hc].
    - pose proof Hc as Hc'. apply andb_prop in Hc'. destruct Hc' as [C1 C2].
      rewrite ltb_spec in C1, C2. change (φ 0) with 0%Z in C1.
      apply (IH (gap (PArray.length us + 1) (steps + 1))); [| reflexivity |].
      + rewrite <- Hz. apply (dij_dec _ _ _ Hc).
      + exact (dij_step U D dn hp sz steps HU DI C1 ltac:(lia)).
    - assert (Hs0 : (φ sz) = 0%Z).
      { destruct (0 <? sz) eqn:E1.
        - destruct (steps <? PArray.length us + 1) eqn:E2; [discriminate|].
          rewrite <- Bool.not_true_iff_false, ltb_spec in E2.
          pose proof (di_count _ _ _ _ _ _ DI) as Hcnt.
          assert (HR0 : (0 <= Rem dn)%Z) by (unfold Rem; apply remc_bound).
          pose proof (to_Z_bounded sz). clear - Hcnt HR0 E2 HL H0. lia.
        - rewrite <- Bool.not_true_iff_false, ltb_spec in E1. change (φ 0) with 0%Z in E1.
          pose proof (to_Z_bounded sz). lia. }
      split; [exact (di_lD _ _ _ _ _ _ DI)|].
      intros y c L Hy Hw.
      destruct (frontier U D dn hp sz steps HU DI y c L Hw) as [[Hd _] | (j & Hj & _)]; [| lia].
      exact (di_done _ _ _ _ _ _ DI y Hy Hd).
  Qed.

  Lemma dij_init : forall u : int, (0 <= (φ u) < N)%Z ->
    dinv (φ u) ((PArray.make n INF).[u <- 0]) (PArray.make n false)
         ((PArray.make (PArray.length us + 1) 0).[0 <- u]) 1 0.
  Proof.
    intros u Hu. pose proof N_wB as HNw. pose proof lim_phi as HL. pose proof INF_val as HI.
    assert (Hn' : ((φ n) <= 4194303)%Z) by (unfold N in *; lia).
    assert (HlD : PArray.length (PArray.make n INF) = n) by (apply alen_make_i; exact Hn').
    assert (Hlh : PArray.length (PArray.make (PArray.length us + 1) 0) = PArray.length us + 1)
      by (apply alen_make_i; rewrite HL; lia).
    assert (AD : forall y, (0 <= y < N)%Z -> at_ (PArray.make n INF).[u <- 0] y = if Z.eqb y (φ u) then 0%Z else (φ INF)).
    { intros y Hy. rewrite at_set by (rewrite ?HlD; unfold N in *; lia). rewrite at_make. reflexivity. }
    assert (Hh0 : at_ (PArray.make (PArray.length us + 1) 0).[0 <- u] 0 = (φ u)).
    { pose proof M_nonneg. rewrite at_set by (rewrite ?Hlh, ?HL; change (φ 0) with 0%Z; lia). reflexivity. }
    constructor.
    - rewrite alen_set_i. exact HlD.
    - apply alen_make_b. exact Hn'.
    - rewrite alen_set_i. exact Hlh.
    - intros j Hj. change (φ 1) with 1%Z in Hj. lia.
    - intros j Hj. change (φ 1) with 1%Z in Hj. assert (j = 0%Z) by lia. subst j.
      rewrite Hh0, Z.mod_small by lia. split; [lia|]. exists [(φ u)].
      rewrite Z.div_small by lia. constructor.
    - intros y Hy Hd. rewrite atb_make in Hd. discriminate.
    - intros y Hy Hd Hne. rewrite AD in Hne |- * by exact Hy.
      destruct (Z.eqb_spec y (φ u)) as [-> | E]; [| congruence].
      exists 0%Z. change (φ 1) with 1%Z. split; [lia | rewrite Hh0; lia].
    - intros a b w _ Hd. rewrite atb_make in Hd. discriminate.
    - intros _. rewrite AD by exact Hu. rewrite Z.eqb_refl. reflexivity.
    - change (φ 0) with 0%Z. change (φ 1) with 1%Z. unfold Rem. rewrite remc_all.
      pose proof M_nonneg. rewrite Z2Nat.id by lia. lia.
  Qed.

  Lemma dijkstra_spec : forall u : int, (0 <= (φ u) < N)%Z ->
    let Dr := dijkstra n (PArray.length us) hd nx vs ws bd p u in
    PArray.length Dr = n /\
    forall y c L, (0 <= y < N)%Z -> pw Erw (φ u) y c L ->
      (exists L', pw Erw (φ u) y (at_ Dr y) L') /\ (forall c' L', pw Erw (φ u) y c' L' -> (at_ Dr y <= c')%Z).
  Proof.
    intros u Hu. cbv zeta. unfold dijkstra.
    apply (dij_loop (φ u) Hu _ 0 _ _ eq_refl). exact (dij_init u Hu).
  Qed.

End Dij.

(* ------------------------------------------------------------------ *)
(* The rows of the answer                                              *)
(* ------------------------------------------------------------------ *)

Definition cell_ok (u v : Z) (a : answer int) : Prop :=
  match a with
  | Impossible => ~ RG u v
  | NegInfinity => forall lo, exists c L, pw Ge u v c L /\ (c < lo)%Z
  | Distance x => (exists L, pw Ge u v (Sint63.to_Z x) L) /\
                  (forall c L, pw Ge u v c L -> (Sint63.to_Z x <= c)%Z)
  end.

Section Rows.
  Variables (hd nx : array int).
  Hypothesis Hhd : forall a, (0 <= a < N)%Z -> at_ hd a = Lb a M.
  Hypothesis Hnx : forall e, (0 <= e < M)%Z -> at_ nx e = Lb (au e) e.

  Let Rx := Rm hd nx.
  Let bx := bad hd nx.
  Let px := pot hd nx.

  Lemma seed_spec : forall u : int, (0 <= (φ u) < N)%Z ->
    let s := for_loop (negseed_step n Rx bx u) 0 n (PArray.make n false) in
    PArray.length s = n /\
    forall a, (0 <= a < N)%Z -> (atb s a = true <-> atb bx a = true /\ RG (φ u) a).
  Proof.
    intros u Hu. cbv zeta.
    pose proof N_wB as HNw.
    set (Inv := fun (k : Z) (s : array bool) => PArray.length s = n /\
       forall a, (0 <= a < N)%Z -> (atb s a = true <-> (a < k)%Z /\ atb bx a = true /\ RG (φ u) a)).
    enough (H : Inv (φ n) (for_loop (negseed_step n Rx bx u) 0 n (PArray.make n false))).
    { destruct H as [H1 H2]. split; [exact H1|]. intros a Ha. rewrite H2 by exact Ha. unfold N in *. tauto. }
    apply for_loop_inv; change (φ 0) with 0%Z; [unfold N in *; lia | |].
    - split; [apply alen_make_b; unfold N in *; lia|]. intros a Ha. rewrite atb_make.
      split; [discriminate | lia].
    - intros a s Ha [L1 L2]. unfold negseed_step.
      assert (Ea : (bx.[a] && Rx.[u * n + a]) = true <-> atb bx (φ a) = true /\ RG (φ u) (φ a)).
      { rewrite andb_true_iff, atb_phi. unfold Rx. rewrite Rm_get by (auto; unfold N in *; lia). reflexivity. }
      destruct (bx.[a] && Rx.[u * n + a]) eqn:Ec.
      + split; [rewrite alen_set_b; exact L1|]. intros y Hy.
        rewrite atb_set by (rewrite ?L1; unfold N in *; lia).
        destruct (Z.eqb_spec y (φ a)) as [-> | Hne].
        * split; [intros _; split; [lia | apply Ea; reflexivity] | auto].
        * rewrite L2 by exact Hy. split; [intros (A & B & C); split; [lia | auto] |].
          intros (A & B & C). split; [lia | auto].
      + split; [exact L1|]. intros y Hy. rewrite L2 by exact Hy.
        split; [intros (A & B & C); split; [lia | auto] |].
        intros (A & B & C). split; [| auto].
        destruct (Z.eq_dec y (φ a)) as [-> | Hne]; [| lia].
        exfalso. assert (Hf : false = true) by (apply Ea; auto). discriminate.
  Qed.

  (* the hypotheses of the Dijkstra section, for the potentials *)
  Lemma dij_hyps :
    PArray.length bx = n /\ PArray.length px = n /\
    (forall a b w, Gs bx a b w -> (sat px b <= sat px a + w)%Z) /\
    (forall v, (0 <= v < N)%Z -> (- 1000 * (N - 1) <= sat px v <= 0)%Z) /\
    (forall x y c L, pw (Gs bx) x y c L -> (0 <= x < N)%Z ->
       exists c' L', pw (Gs bx) x y c' L' /\ (c' <= c)%Z /\ (Z.of_nat (List.length L') <= N)%Z).
  Proof.
    destruct (bad_spec hd nx Hhd Hnx) as [B1 _].
    destruct (pot_spec hd nx Hhd Hnx) as (Q1 & _ & _ & Q4 & Q5).
    split; [exact B1 | split; [exact Q1 | split; [exact Q4 | split; [exact Q5 |]]]].
    exact (G2_shorten hd nx Hhd Hnx).
  Qed.

  Lemma row_spec : forall u : int, (0 <= (φ u) < N)%Z ->
    let r := row_of n (PArray.length us) hd nx vs ws Rx bx px u in
    PArray.length r = n /\ forall v : int, (0 <= (φ v) < N)%Z -> cell_ok (φ u) (φ v) (r.[v]).
  Proof.
    intros u Hu. cbv zeta. unfold row_of.
    pose proof N_wB as HNw.
    destruct dij_hyps as (Hlb & Hlp & Hfeas & Hpb & Hshort).
    destruct (seed_spec u Hu) as [Ls Hs].
    set (seed := for_loop (negseed_step n Rx bx u) 0 n (PArray.make n false)) in *.
    destruct (closure_spec hd nx Hhd Hnx seed Ls) as [Lneg Hneg].
    set (neg := closure n hd nx vs seed) in *.
    destruct (dijkstra_spec hd nx Hhd Hnx bx px Hlb Hlp Hfeas Hpb Hshort u Hu) as [LD HD].
    set (D := dijkstra n (PArray.length us) hd nx vs ws bx px u) in *.
    (* the facts about one cell *)
    assert (Cell : forall v : int, (0 <= (φ v) < N)%Z -> cell_ok (φ u) (φ v) (cell n Rx neg D px u v)).
    { intros v Hv. unfold cell.
      destruct (neg.[v]) eqn:En.
      - (* a negative cycle between u and v *)
        rewrite <- atb_phi in En. apply Hneg in En; [| exact Hv].
        destruct En as (x & Hx & Hsx & Hxv). apply Hs in Hsx; [| exact Hx]. destruct Hsx as [Hbx Hux].
        destruct (bad_neg hd nx Hhd Hnx x Hx Hbx) as (c0 & L0 & Hl & Hc0).
        exact (neg_loop_short x (φ u) (φ v) c0 L0 Hl Hc0 Hux Hxv).
      - assert (Hnn : forall x, (0 <= x < N)%Z -> atb bx x = true -> RG (φ u) x -> RG x (φ v) -> False).
        { intros x Hx Hb Hux Hxv. rewrite <- atb_phi in En.
          assert (atb neg (φ v) = true) by (apply Hneg; [exact Hv | exists x; split; [exact Hx | split; [apply Hs; auto | exact Hxv]]]).
          congruence. }
        destruct (Rx.[u * n + v]) eqn:Er.
        + unfold Rx in Er. rewrite Rm_get in Er by auto.
          (* every walk from u to v avoids the bad vertices *)
          assert (Hgood : forall c L, pw Ge (φ u) (φ v) c L -> pw (Gs bx) (φ u) (φ v) c L).
          { intros c L H. apply (pw_restrict Ge (Gs bx) _ _ _ _ H).
            intros a b w He Ha Hb. split; [exact He|].
            destruct (Ge_bounds a b w He) as [Ha' Hb'].
            destruct (pw_in_R Ge _ _ _ _ a H Ha) as [Hua Hav].
            destruct (pw_in_R Ge _ _ _ _ b H Hb) as [Hub Hbv].
            split; [destruct (atb bx a) eqn:E; [exfalso; eapply Hnn; eauto | reflexivity] |
                    destruct (atb bx b) eqn:E; [exfalso; eapply Hnn; eauto | reflexivity]]. }
          destruct Er as (c0 & L0 & H0).
          pose proof (rw_of bx px Hlb Hlp _ _ _ _ (Hgood _ _ H0)) as Hrw.
          destruct (HD (φ v) _ _ Hv Hrw) as [[L1 HW1] Hopt].
          destruct (of_rw bx px Hlb Hlp _ _ _ _ HW1) as (c1 & Hc1 & Ec1).
          pose proof (Hpb (φ u) Hu) as Hpu. pose proof (Hpb (φ v) Hv) as Hpv.
          (* bounds on the distance *)
          assert (Hlo : forall c L, pw Ge (φ u) (φ v) c L -> (c1 <= c)%Z).
          { intros c L H. pose proof (Hopt _ _ (rw_of bx px Hlb Hlp _ _ _ _ (Hgood _ _ H))). lia. }
          destruct (Hshort _ _ _ _ Hc1 Hu) as (c2 & L2 & H2 & Hc2 & Hl2).
          pose proof (pw_cost (Gs bx) (-1000) 1000 ltac:(intros a b w0 He; eapply Ge_w; apply (Gf_Ge _ _ _ _ He)) _ _ _ _ H2) as Hcost.
          pose proof (pw_len_pos _ _ _ _ _ H2).
          pose proof (Hlo c2 L2 (pw_mono _ _ (Gf_Ge _) _ _ _ _ H2)).
          assert (Hc1b : (- 1000 * N <= c1 <= 1000 * N)%Z) by nia.
          assert (EDv : Sint63.to_Z (D.[v]) = at_ D (φ v)) by (rewrite s_of_u; [unfold at_; rewrite of_to_Z; reflexivity | unfold at_ in *; rewrite of_to_Z in *; lia]).
          assert (EPu : Sint63.to_Z (px.[u]) = sat px (φ u)) by (rewrite sat_phi; reflexivity).
          assert (EPv : Sint63.to_Z (px.[v]) = sat px (φ v)) by (rewrite sat_phi; reflexivity).
          assert (Ex : Sint63.to_Z (D.[v] - px.[u] + px.[v]) = c1).
          { rewrite s_add; rewrite ?s_sub; rewrite ?EDv, ?EPu, ?EPv; try lia;
              rewrite ?s_sub; rewrite ?EDv, ?EPu, ?EPv; lia. }
          simpl. rewrite Ex. split; [exists L1; exact (pw_mono _ _ (Gf_Ge _) _ _ _ _ Hc1) | exact Hlo].
        + simpl. intros Hr. unfold Rx in Er. rewrite <- Bool.not_true_iff_false, Rm_get in Er by auto.
          contradiction. }
    set (Inv := fun (k : Z) (r : array (answer int)) => PArray.length r = n /\
       forall v : int, (0 <= (φ v) < k)%Z -> r.[v] = cell n Rx neg D px u v).
    enough (H : Inv (φ n) (for_loop (fun v r => r.[v <- cell n Rx neg D px u v]) 0 n (PArray.make n Impossible))).
    { destruct H as [H1 H2]. split; [exact H1|]. intros v Hv. rewrite H2 by (unfold N in *; lia). apply Cell. exact Hv. }
    apply for_loop_inv; change (φ 0) with 0%Z; [unfold N in *; lia | |].
    - split; [apply alen_make_a; unfold N in *; lia | intros v Hv; lia].
    - intros v r Hv [L1 L2]. split; [rewrite alen_set_a; exact L1|].
      intros v' Hv'. destruct (Z.eq_dec (φ v') (φ v)) as [E | E].
      + apply phi_inj in E. subst v'. apply aget_set_same_a. rewrite L1, ltb_spec. lia.
      + rewrite aget_set_other_a by (intro F; apply E; rewrite F; reflexivity). apply L2. lia.
  Qed.
End Rows.

Lemma impl_spec :
  let res := allpairspath_impl n us vs ws in
  PArray.length res = n /\
  forall u v : int, (0 <= (φ u) < N)%Z -> (0 <= (φ v) < N)%Z ->
    PArray.length (res.[u]) = n /\ cell_ok (φ u) (φ v) (res.[u].[v]).
Proof.
  cbv zeta.
  destruct (build_adj n (PArray.length us) us) as [hd nx] eqn:Eb.
  destruct (build_adj_spec hd nx Eb) as (_ & _ & Hhd & Hnx).
  assert (E : allpairspath_impl n us vs ws =
    for_loop (fun u res => res.[u <- row_of n (PArray.length us) hd nx vs ws (Rm hd nx) (bad hd nx) (pot hd nx) u])
      0 n (PArray.make n (PArray.make 0 Impossible))).
  { unfold allpairspath_impl. cbv zeta. rewrite Eb. reflexivity. }
  rewrite E.
  set (Inv := fun (k : Z) (r : array (array (answer int))) => PArray.length r = n /\
     forall u : int, (0 <= (φ u) < k)%Z ->
       r.[u] = row_of n (PArray.length us) hd nx vs ws (Rm hd nx) (bad hd nx) (pot hd nx) u).
  enough (H : Inv (φ n) (for_loop (fun u res => res.[u <- row_of n (PArray.length us) hd nx vs ws (Rm hd nx) (bad hd nx) (pot hd nx) u])
      0 n (PArray.make n (PArray.make 0 Impossible)))).
  { destruct H as [H1 H2]. split; [exact H1|]. intros u v Hu Hv.
    rewrite H2 by (unfold N in *; lia).
    destruct (row_spec hd nx Hhd Hnx u Hu) as [R1 R2]. split; [exact R1 | apply R2; exact Hv]. }
  apply for_loop_inv; change (φ 0) with 0%Z; [unfold N in *; lia | |].
  - split; [apply alen_make_r; unfold N in *; lia | intros u Hu; lia].
  - intros u r Hu [L1 L2]. split; [rewrite alen_set_r; exact L1|].
    intros u' Hu'. destruct (Z.eq_dec (φ u') (φ u)) as [E' | E'].
    + apply phi_inj in E'. subst u'. apply aget_set_same_r. rewrite L1, ltb_spec. lia.
    + rewrite aget_set_other_r by (intro F; apply E'; rewrite F; reflexivity). apply L2. lia.
Qed.

End Graph.

(* ------------------------------------------------------------------ *)
(* From the spec's lists to the arrays, and back                       *)
(* ------------------------------------------------------------------ *)

Lemma repr_len_u : forall (x : array uint) (l : list BinNums.N), repr x l ->
  (φ (PArray.length x)) = Z.of_nat (List.length l).
Proof. intros x l [H _]. symmetry. exact H. Qed.

Lemma repr_len_s : forall (x : array sint) (l : list Z), repr x l ->
  (φ (PArray.length x)) = Z.of_nat (List.length l).
Proof. intros x l [H _]. symmetry. exact H. Qed.

Lemma repr_at_u : forall (x : array uint) (l : list BinNums.N), repr x l ->
  forall k, (0 <= k < Z.of_nat (List.length l))%Z -> at_ x k = Z.of_N (nth (Z.to_nat k) l 0%N).
Proof.
  intros x l [_ Hc] k Hk. destruct (Hc (Z.to_nat k) ltac:(lia)) as (a & Ha & Hr).
  rewrite (nth_error_nth _ _ _ Ha). unfold repr, repr_uint in Hr. rewrite <- Hr.
  rewrite Z2Nat.id in Hr |- * by lia. unfold at_.
  pose proof (to_Z_bounded (x.[of_Z k])). rewrite Z2N.id by lia. reflexivity.
Qed.

Lemma repr_at_s : forall (x : array sint) (l : list Z), repr x l ->
  forall k, (0 <= k < Z.of_nat (List.length l))%Z -> Sint63.to_Z (x.[of_Z k]) = nth (Z.to_nat k) l 0%Z.
Proof.
  intros x l [_ Hc] k Hk. destruct (Hc (Z.to_nat k) ltac:(lia)) as (a & Ha & Hr).
  rewrite (nth_error_nth _ _ _ Ha). unfold repr, repr_sint in Hr. rewrite <- Hr.
  rewrite Z2Nat.id by lia. reflexivity.
Qed.

Definition amath (a : answer int) : answer Z :=
  match a with
  | Impossible => Impossible
  | NegInfinity => NegInfinity
  | Distance x => Distance (Sint63.to_Z x)
  end.

Lemma repr_amath : forall a : answer sint, repr a (amath a).
Proof. intros [| | x]; simpl; reflexivity. Qed.

Definition out_list (n : int) (res : array (array (answer int))) : list (list (answer Z)) :=
  map (fun u => map (fun v => amath (res.[of_Z (Z.of_nat u)].[of_Z (Z.of_nat v)]))
                    (seq 0 (Z.to_nat (φ n))))
      (seq 0 (Z.to_nat (φ n))).

Section Final.
  Variables (nN : BinNums.N) (lu lv : list BinNums.N) (lw : list Z) (xn : uint) (xu xv : array uint) (xw : array sint).
  Hypothesis Hvi : valid_input nN lu lv lw.
  Hypothesis Hrn : repr xn nN.
  Hypothesis Hru : repr xu lu.
  Hypothesis Hrv : repr xv lv.
  Hypothesis Hrw : repr xw lw.

  Lemma Fn : (φ xn) = Z.of_N nN.
  Proof. unfold repr, repr_uint in Hrn. rewrite <- Hrn. pose proof (to_Z_bounded xn). lia. Qed.

  Lemma Flens : (φ (PArray.length xu)) = Z.of_nat (List.length lu) /\
                PArray.length xv = PArray.length xu /\ PArray.length xw = PArray.length xu.
  Proof.
    destruct Hvi as [_ _ Hlv Hlw _ _]. unfold len in Hlv, Hlw.
    pose proof (repr_len_u xu lu Hru) as A. pose proof (repr_len_u xv lv Hrv) as B.
    pose proof (repr_len_s xw lw Hrw) as C.
    split; [exact A | split; apply phi_inj].
    - transitivity (Z.of_nat (List.length lv)); [exact B|].
      transitivity (Z.of_nat (List.length lu)); [lia | symmetry; exact A].
    - transitivity (Z.of_nat (List.length lw)); [exact C|].
      transitivity (Z.of_nat (List.length lu)); [lia | symmetry; exact A].
  Qed.

  Lemma au_list : forall k, (0 <= k < Z.of_nat (List.length lu))%Z ->
    au xu k = Z.of_N (nth (Z.to_nat k) lu 0%N).
  Proof. intros k Hk. exact (repr_at_u xu lu Hru k Hk). Qed.
  Lemma av_list : forall k, (0 <= k < Z.of_nat (List.length lv))%Z ->
    av xv k = Z.of_N (nth (Z.to_nat k) lv 0%N).
  Proof. intros k Hk. exact (repr_at_u xv lv Hrv k Hk). Qed.
  Lemma aw_list : forall k, (0 <= k < Z.of_nat (List.length lw))%Z ->
    aw xw k = nth (Z.to_nat k) lw 0%Z.
  Proof. intros k Hk. exact (repr_at_s xw lw Hrw k Hk). Qed.

  (* math edges are machine edges *)
  Lemma edge_Ge : forall a b w, edge lu lv lw a b w <-> Ge xu xv xw (Z.of_N a) (Z.of_N b) w.
  Proof.
    destruct Flens as (Lu & _ & _).
    assert (LuM : M xu = Z.of_nat (List.length lu)) by exact Lu.
    destruct Hvi as [_ _ Hlv Hlw _ _]. unfold len in Hlv, Hlw.
    intros a b w. unfold edge, Ge, edge_index, len, get_list_N, get_list_Z. split.
    - intros (k & Hk & Ea & Eb & Ew). exists (Z.of_N k). split; [lia|].
      rewrite au_list by lia. rewrite av_list by lia. rewrite aw_list by lia.
      replace (Z.to_nat (Z.of_N k)) with (N.to_nat k) by lia. subst. auto.
    - intros (k & Hk & Ea & Eb & Ew). exists (Z.to_N k). split; [lia|].
      rewrite au_list in Ea by lia. rewrite av_list in Eb by lia. rewrite aw_list in Ew by lia.
      rewrite Z_N_nat. split; [lia | split; [lia | exact Ew]].
  Qed.

  Lemma walk_pw : forall u v c, walk lu lv lw u v c -> exists L, pw (Ge xu xv xw) (Z.of_N u) (Z.of_N v) c L.
  Proof.
    intros u v c H. induction H as [| v v' w c H IH He].
    - exists [Z.of_N u]. constructor.
    - destruct IH as [L HL]. exists (Z.of_N v' :: L). econstructor; [exact HL | apply edge_Ge; exact He].
  Qed.

  Lemma pw_walk : forall u y c L, pw (Ge xu xv xw) (Z.of_N u) y c L -> (0 <= y)%Z /\ walk lu lv lw u (Z.to_N y) c.
  Proof.
    intros u y c L H. induction H as [| v v' w c L H IH He].
    - split; [lia|]. rewrite N2Z.id. constructor.
    - destruct IH as [Hv Hw].
      assert (Hv' : (0 <= v')%Z) by (destruct He as (k & _ & _ & <- & _); unfold av, at_; pose proof (to_Z_bounded (xv.[of_Z k])); lia).
      split; [exact Hv'|]. econstructor; [exact Hw|]. apply edge_Ge. rewrite !Z2N.id by lia. exact He.
  Qed.

  Lemma pw_walk' : forall u v c L, pw (Ge xu xv xw) (Z.of_N u) (Z.of_N v) c L -> walk lu lv lw u v c.
  Proof. intros u v c L H. destruct (pw_walk u _ c L H) as [_ W]. rewrite N2Z.id in W. exact W. Qed.

  Lemma final_correct : exists m,
    repr (allpairspath_impl xn xu xv xw : array (array (answer sint))) m /\ allpairspath_spec nN lu lv lw m.
  Proof.
    pose proof Fn as HFn. destruct Flens as (Lu & Lv & Lw).
    pose proof Hvi as Hvi'. destruct Hvi' as [Hn Hm _ _ Hend Hwt]. unfold len in Hm.
    assert (LuM : M xu = Z.of_nat (List.length lu)) by exact Lu.
    assert (HnZ : (1 <= N xn <= 150)%Z) by (unfold N; lia).
    assert (HMZ : (M xu <= 5000)%Z) by lia.
    assert (Hend' : forall k, (0 <= k < M xu)%Z ->
              (0 <= au xu k < N xn /\ 0 <= av xv k < N xn)%Z).
    { intros k Hk. rewrite LuM in Hk. unfold N.
      destruct (Hend (Z.to_N k) ltac:(unfold edge_index, len; lia)) as [A B].
      unfold vertex, get_list_N in A, B. rewrite Z_N_nat in A, B.
      rewrite au_list by lia. rewrite av_list by (destruct Hvi as [_ _ X _ _ _]; unfold len in X; lia).
      lia. }
    assert (Hwt' : forall k, (0 <= k < M xu)%Z -> (-1000 <= aw xw k <= 1000)%Z).
    { intros k Hk. rewrite LuM in Hk.
      destruct Hvi as [_ _ _ X _ _]. unfold len in X.
      rewrite aw_list by lia.
      rewrite Forall_forall in Hwt. apply Hwt. apply nth_In. lia. }
    destruct (impl_spec xn xu xv xw HnZ HMZ Lv Lw Hend' Hwt') as [R1 R2].
    set (res := allpairspath_impl xn xu xv xw) in *.
    exists (out_list xn res).
    assert (Hlo : List.length (out_list xn res) = N.to_nat nN).
    { unfold out_list. rewrite length_map, length_seq. lia. }
    assert (Hrow : forall u, (u < N.to_nat nN)%nat ->
       nth_error (out_list xn res) u =
       Some (map (fun v => amath (res.[of_Z (Z.of_nat u)].[of_Z (Z.of_nat v)])) (seq 0 (N.to_nat nN)))).
    { intros u Hu. unfold out_list. rewrite nth_error_map, nth_error_seq.
      replace (Z.to_nat (φ xn)) with (N.to_nat nN) by lia.
      destruct (Nat.ltb_spec u (N.to_nat nN)); [reflexivity | lia]. }
    assert (Hcell : forall u v, (u < N.to_nat nN)%nat -> (v < N.to_nat nN)%nat ->
       nth_error (map (fun v => amath (res.[of_Z (Z.of_nat u)].[of_Z (Z.of_nat v)])) (seq 0 (N.to_nat nN))) v =
       Some (amath (res.[of_Z (Z.of_nat u)].[of_Z (Z.of_nat v)]))).
    { intros u v Hu Hv. rewrite nth_error_map, nth_error_seq.
      destruct (Nat.ltb_spec v (N.to_nat nN)); [reflexivity | lia]. }
    assert (Hph : forall k, (k < N.to_nat nN)%nat -> (φ (of_Z (Z.of_nat k))) = Z.of_nat k).
    { intros k Hk. apply of_Z_phi. rewrite wB_val. lia. }
    split.
    - (* repr *)
      split.
      + rewrite Hlo. assert (R1' : (φ (PArray.length res)) = Z.of_nat (N.to_nat nN)) by (rewrite R1; lia).
        symmetry. exact R1'.
      + intros u Hu. rewrite Hlo in Hu. eexists. split; [apply Hrow; exact Hu|].
        destruct (R2 (of_Z (Z.of_nat u)) 0 ltac:(rewrite Hph by exact Hu; unfold N; lia)
                    ltac:(change (φ 0) with 0%Z; unfold N; lia)) as [Rl _].
        split.
        * rewrite length_map, length_seq.
          assert (Rl' : (φ (PArray.length (res.[of_Z (Z.of_nat u)]))) = Z.of_nat (N.to_nat nN)) by (rewrite Rl; lia).
          symmetry. exact Rl'.
        * intros v Hv. rewrite length_map, length_seq in Hv. eexists. split; [apply Hcell; auto|].
          apply repr_amath.
    - (* the spec *)
      split; [unfold len; rewrite Hlo; lia|].
      intros u Hu. unfold vertex in Hu.
      unfold get_list_row. rewrite (nth_error_nth _ _ _ (Hrow (N.to_nat u) ltac:(lia))).
      split; [unfold len; rewrite length_map, length_seq; lia|].
      intros v Hv. unfold vertex in Hv. unfold get_list_answer.
      rewrite (nth_error_nth _ _ _ (Hcell (N.to_nat u) (N.to_nat v) ltac:(lia) ltac:(lia))).
      rewrite !N_nat_Z.
      destruct (R2 (of_Z (Z.of_N u)) (of_Z (Z.of_N v)) ltac:(rewrite of_Z_phi; unfold N; rewrite ?wB_val; lia)
                  ltac:(rewrite of_Z_phi; unfold N; rewrite ?wB_val; lia)) as [_ C].
      rewrite !of_Z_phi in C by (rewrite wB_val; lia).
      destruct (res.[of_Z (Z.of_N u)].[of_Z (Z.of_N v)]) as [| | x]; simpl in C |- *.
      + intros (c & Hw). apply C. destruct (walk_pw u v c Hw) as [L HL]. exists c, L. exact HL.
      + intros lo. destruct (C lo) as (c & L & HL & Hc). exists c. split; [exact (pw_walk' u v c L HL) | exact Hc].
      + destruct C as [[L HL] Hopt]. split; [exact (pw_walk' u v _ L HL)|].
        intros c Hw. destruct (walk_pw u v c Hw) as [L' HL']. exact (Hopt c L' HL').
  Qed.
End Final.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition allpairspath : uint -> array uint -> array uint -> array sint ->
                            array (array (answer sint)) := allpairspath_impl.
Elpi complexity allpairspath.

Definition allpairspath_correct :
  forall (n : BinNums.N) (us vs : list BinNums.N) (ws : list Z)
         (xn : uint) (xu xv : array uint) (xw : array sint),
  valid_input n us vs ws ->
  repr xn n -> repr xu us -> repr xv vs -> repr xw ws ->
  exists m : list (list (answer Z)),
    repr (allpairspath xn xu xv xw) m /\ allpairspath_spec n us vs ws m
  := final_correct.


(* ====================================================================== *)
(* Cost: allpairspath_time                                                *)
(* ====================================================================== *)

(* The cost twins (allpairspath_cost and its callees') are defined by the
   [Elpi complexity] lines next to the program.  The proof below: a lemma
   per loop (for_acc / for_loop with a uniform bound per iteration, the
   edge chains of the forward star by the count cnt of the edges left, the
   heap sifts by the depth, the breadth-first search with the potential
   remc + QW, Dijkstra with the potential Rem of the edges whose source is
   not final, the remaining steps bounded by the lim = m + 1 pops), then
   the phases and allpairspath_time. *)

Arguments Uint63Axioms.to_Z : simpl never.

(* ---- cbase.v ---- *)
Lemma pow2S k : (2 ^ Z.of_nat (S k) = 2 * 2 ^ Z.of_nat k)%Z.
Proof. rewrite Nat2Z.inj_succ; apply Z.pow_succ_r; lia. Qed.

Lemma bdec_time b (w : bool_cost stepsCM b) : (cost (bdec_cost stepsCM b w) <= 2)%nat.
Proof. destruct w; cbn; lia. Qed.

Lemma for_acc_time S SC f fC (K : nat) :
  (forall i iC s sC, (cost (fC i iC) + cost (extract (fC i iC) s sC) <= K)%nat) ->
  forall hi hiC i iC s sC H HC,
  (cost (extract (extract (extract (extract (extract (for_acc_cost stepsCM S SC) f fC) hi hiC) i iC) s sC) H HC)
    <= (K + 20) * Z.to_nat (gap hi i) + 10)%nat.
Proof.
  intros HK hi hiC i iC s sC H HC.
  unfold for_acc_cost. cbn.
  match goal with |- context [@cost ?T (?G hi hiC i iC s sC H HC)] =>
    assert (HG : forall k i iC s sC H HC, (Z.to_nat (gap hi i) <= k)%nat ->
       (cost (G hi hiC i iC s sC H HC) <= (K + 20) * k + 10)%nat) end.
  { induction k as [|k IH]; intros i' iC' s' sC' [g] HC' Hk;
      cost_simpl;
      pose proof (bdec_time (i' <? hi) (bool_w (i' <? hi))) as HB;
      cost_destruct (bdec (i' <? hi)); cost_simpl.
    - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e). unfold gap in Hk. lia.
    - lia.
    - pose proof (proj1 (Uint63.ltb_spec _ _) e) as Hlt.
      assert (Hk' : (Z.to_nat (gap hi (i' + 1)) <= k)%nat).
      { unfold gap in *. assert (φ (i' + 1) = φ i' + 1)%Z by (zify; Z.to_euclidean_division_equations; lia). lia. }
      match goal with |- context [@cost ?T (?G' hi hiC (i' + 1)%uint63 ?w ?s2 ?sc2 ?h ?e2)] =>
          pose proof (IH (i' + 1)%uint63 w s2 sc2 h e2 Hk' : (@cost T (G' hi hiC (i' + 1)%uint63 w s2 sc2 h e2) <= _)%nat) as HI end.
      specialize (HK i' iC' s' sC'). cost_align HK. lia.
    - lia. }
  match goal with |- context [@cost ?T (?G hi hiC i iC s sC H HC)] =>
    exact (HG _ i iC s sC H HC (le_n _) : (@cost T (G hi hiC i iC s sC H HC) <= _)%nat) end.
Qed.

Ltac is_layer F m d :=
  lazymatch d with
  | Datatypes.S ?d' =>
      lazymatch m with
      | F _ => idtac
      | F _ _ _ => idtac
      | @extract _ _ ?m' _ _ => is_layer F m' d'
      end
  end.
Ltac is_layer_exact F m d :=
  lazymatch d with
  | Datatypes.O =>
      lazymatch m with
      | F _ => idtac
      | F _ _ _ => idtac
      end
  | Datatypes.S ?d' => lazymatch m with @extract _ _ ?m' _ _ => is_layer_exact F m' d' end
  end.
Ltac ztop F d := repeat match goal with |- context [@cost ?T ?m] => is_layer_exact F m d; change (@cost T m) with 1%nat end.
Ltac zl F d := repeat match goal with |- context [@cost ?T ?m] => is_layer F m d; change (@cost T m) with 0%nat end.

Ltac cost_align_any := match goal with H : _ |- _ => cost_align H end.
Lemma for_loop_time S SC f fC (K : nat) :
  (forall i iC s sC, (cost (fC i iC) + cost (extract (fC i iC) s sC) <= K)%nat) ->
  forall lo loC hi hiC s sC,
  (cost (extract (extract (extract (extract (for_loop_cost stepsCM S SC) f fC) lo loC) hi hiC) s sC)
    <= (K + 20) * Z.to_nat (gap hi lo) + 20)%nat.
Proof.
  intros HK lo loC hi hiC s sC.
  unfold for_loop_cost. cost_simpl. zl for_acc_cost 5%nat.
  match goal with |- context [@cost ?T (extract (extract (extract (extract (extract (for_acc_cost stepsCM S SC) f fC) hi hiC) lo loC) s sC) ?h ?hc)] =>
    pose proof (for_acc_time S SC f fC K HK hi hiC lo loC s sC h hc : (@cost T (extract (extract (extract (extract (extract (for_acc_cost stepsCM S SC) f fC) hi hiC) lo loC) s sC) h hc) <= _)%nat) as HI end.
  lia.
Qed.

Lemma adj_step_time us usC k kC st stC :
  (cost (adj_step_cost stepsCM us usC) + cost (extract (adj_step_cost stepsCM us usC) k kC) +
   cost (extract (extract (adj_step_cost stepsCM us usC) k kC) st stC) <= 30)%nat.
Proof.
  destruct stC as [hd hdC nx nxC].
  unfold adj_step_cost. cost_simpl.
  zl set_cost 3%nat. ztop set_cost 3%nat. lia.
Qed.

Lemma build_adj_time n nC m mC us usC :
  (cost (extract (extract (build_adj_cost stepsCM n nC) m mC) us usC) <= 60 * Z.to_nat (φ m) + 40)%nat.
Proof.
  match goal with |- (_ <= ?r)%nat => remember r as RHS eqn:ER end.
  unfold build_adj_cost. cost_simpl.
  zl for_loop_cost 4%nat. zl adj_step_cost 2%nat. zl make_cost 2%nat. ztop make_cost 2%nat.
  match goal with |- context [@cost ?T (extract (extract (extract (extract (for_loop_cost stepsCM ?S ?SC) ?f ?fC) ?lo ?loC) ?hi ?hiC) ?s ?sC)] =>
    pose proof (for_loop_time S SC f fC 30 ltac:(intros i iC s0 sC0; pose proof (adj_step_time us usC i iC s0 sC0) as HA; cost_align HA; lia) lo loC hi hiC s sC : (@cost T (extract (extract (extract (extract (for_loop_cost stepsCM S SC) f fC) lo loC) hi hiC) s sC) <= _)%nat) as HI end.
  unfold gap in HI. change (φ 0) with 0%Z in HI. rewrite Z.sub_0_r in HI. subst RHS. lia.
Qed.

Lemma chain_fold_time_gen S SC nx nxC f fC cur curC s sC (B : nat) :
  (forall H HC, cost (extract (extract (extract (extract (extract (chain_acc_cost stepsCM S SC) nx nxC) f fC) cur curC) s sC) H HC) <= B)%nat ->
  (cost (extract (extract (extract (extract (chain_fold_cost stepsCM S SC) nx nxC) f fC) cur curC) s sC) <= B + 20)%nat.
Proof.
  intros HB. unfold chain_fold_cost. cost_simpl. zl chain_acc_cost 5%nat.
  match goal with |- context [@cost ?T (extract (extract (extract (extract (extract (chain_acc_cost stepsCM S SC) nx nxC) f fC) cur curC) s sC) ?h ?hc)] =>
    pose proof (HB h hc : (@cost T (extract (extract (extract (extract (extract (chain_acc_cost stepsCM S SC) nx nxC) f fC) cur curC) s sC) h hc) <= _)%nat) as HI end.
  lia.
Qed.

Lemma swap_time t tC i iC j jC :
  (cost (extract (extract (swap_cost stepsCM t tC) i iC) j jC) <= 20)%nat.
Proof.
  unfold swap_cost. cost_simpl. zl set_cost 3%nat. ztop set_cost 3%nat. lia.
Qed.

Ltac gen_swap := repeat match goal with |- context [@cost ?TT ?X] =>
  lazymatch X with extract (extract (swap_cost stepsCM ?t ?tC) ?i ?iC) ?j ?jC =>
    let Hc := fresh "Hc" in
    pose proof (swap_time t tC i iC j jC : (@cost TT X <= _)%nat) as Hc;
    revert Hc; generalize (@cost TT X); intros ? Hc end end.

Lemma sift_up_time : forall k t tC i iC H HC, (φ i < 2 ^ Z.of_nat k)%Z ->
  (cost (extract (extract (sift_up_cost stepsCM t tC) i iC) H HC) <= k * 80 + 20)%nat.
Proof.
  intros k0 t tC i iC H HC Hk.
  unfold sift_up_cost. cbn.
  match goal with |- context [@cost ?T (?G t tC i iC H HC)] =>
    assert (HG : forall k t tC i iC H HC, (φ i < 2 ^ Z.of_nat k)%Z ->
       (cost (G t tC i iC H HC) <= k * 80 + 20)%nat) end.
  { induction k as [|k IH]; intros t' tC' i' iC' [g] HC' Hk';
      cost_simpl;
      pose proof (bdec_time (0 <? i') (bool_w (0 <? i'))) as HB;
      cost_destruct (bdec (0 <? i')); cost_simpl.
    - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e). change (φ 0) with 0%Z in *. cbn in Hk'. lia.
    - lia.
    - pose proof (proj1 (Uint63.ltb_spec _ _) e) as Hlt. change (φ 0) with 0%Z in Hlt.
      assert (Hp : (φ ((i' - 1) / 2) < 2 ^ Z.of_nat k)%Z).
      { assert (E2 : (2 ^ Z.of_nat (S k) = 2 * 2 ^ Z.of_nat k)%Z) by (rewrite Nat2Z.inj_succ; apply Z.pow_succ_r; lia).
        rewrite E2 in Hk'. zify. Z.to_euclidean_division_equations. nia. }
      cost_destruct (t'.[i'] <? t'.[(i' - 1) / 2]); cost_simpl; zl swap_cost 2%nat; gen_swap.
      + match goal with |- context [@cost ?T (?G' ?t2 ?tc2 ((i' - 1) / 2)%uint63 ?w ?h ?e2)] =>
          pose proof (IH t2 tc2 ((i' - 1) / 2)%uint63 w h e2 Hp : (@cost T (G' t2 tc2 ((i' - 1) / 2)%uint63 w h e2) <= _)%nat) as HIH;
          revert HIH; generalize (@cost T (G' t2 tc2 ((i' - 1) / 2)%uint63 w h e2)); intros ? HIH end.
        lia.
      + lia.
    - lia. }
  match goal with |- context [@cost ?T (?G t tC i iC H HC)] =>
    exact (HG _ t tC i iC H HC Hk : (@cost T (G t tC i iC H HC) <= _)%nat) end.
Qed.

Ltac gen_with T X pf := let Hc := fresh "Hc" in pose proof (pf : (@cost T X <= _)%nat) as Hc; revert Hc; generalize (@cost T X); intros ? Hc.

Lemma dbl1 i : (φ i <= 2 ^ 40)%Z -> φ (2 * i + 1) = (2 * φ i + 1)%Z.
Proof. intros H. pose proof (to_Z_bounded i). zify. Z.to_euclidean_division_equations. lia. Qed.
Lemma dbl2 i : (φ i <= 2 ^ 40)%Z -> φ (2 * i + 1 + 1) = (2 * φ i + 2)%Z.
Proof. intros H. pose proof (to_Z_bounded i). zify. Z.to_euclidean_division_equations. lia. Qed.

Ltac cbn_w := repeat match goal with w : ?T |- _ =>
  lazymatch T with
  | bool_cost _ _ => progress cbn in w
  | int_cost _ _ => progress cbn in w
  | array_cost _ _ _ _ => progress cbn in w
  | sumbool_cost _ _ _ _ _ _ => progress cbn in w
  end end.

Ltac hide_fix f := try match goal with |- context [@cost _ ?X] =>
  match X with context [?F] =>
    lazymatch type of F with
    | forall _, _ => lazymatch type of F with context [f] => is_fix F; let F' := fresh "F" in set (F' := F) in *; clearbody F' end
    end end end.

Ltac cost_simpl_h f := cbn; hide_fix f; cost_reduce; fold_cost; repeat (cost_rewrite; cost_reduce); cbn; fold_cost.

Ltac zero_if b := match goal with |- context [@cost ?T ?X] =>
  let E := fresh "E" in assert (E : @cost T X = 0%nat) by (destruct b; reflexivity); rewrite E; clear E end.

Lemma sift_down_time : forall k t tC s sC i iC H HC,
  (φ s < 2 ^ Z.of_nat k * (φ i + 1))%Z -> (φ i <= φ s <= 2 ^ 40)%Z ->
  (cost (extract (extract (extract (sift_down_cost stepsCM t tC) s sC) i iC) H HC) <= k * 100 + 50)%nat.
Proof.
  intros k0 t tC s sC i iC H HC Hk Hb.
  unfold sift_down_cost. cbn.
  match goal with |- context [@cost ?T (?G t tC s sC i iC H HC)] =>
    assert (HG : forall k t tC i iC H HC, (φ s < 2 ^ Z.of_nat k * (φ i + 1))%Z -> (φ i <= φ s <= 2 ^ 40)%Z ->
       (cost (G t tC s sC i iC H HC) <= k * 100 + 50)%nat) end.
  { induction k as [|k IH]; intros t' tC' i' iC' [g] HC' Hk' Hb';
      cost_simpl_h sift_down.
    - cost_destruct_eqn (2 * i' + 1 <? s) El; cost_simpl.
      + exfalso. rewrite ltb_spec in El. rewrite dbl1 in El; [lia|]. change (2 ^ Z.of_nat 0)%Z with 1%Z in Hk'. lia.
      + lia.
    - assert (E2 : (2 ^ Z.of_nat (S k) = 2 * 2 ^ Z.of_nat k)%Z) by (rewrite Nat2Z.inj_succ; apply Z.pow_succ_r; lia).
      rewrite E2 in Hk'. pose proof (dbl1 i' ltac:(lia)) as D1. pose proof (dbl2 i' ltac:(lia)) as D2.
      pose proof (Z.pow_pos_nonneg 2 (Z.of_nat k) ltac:(lia) ltac:(lia)) as Pk.
      cost_destruct_eqn (2 * i' + 1 <? s) El; cost_simpl; [| lia].
      cost_destruct_eqn (2 * i' + 1 + 1 <? s) Er; cost_simpl;
        [cost_destruct_eqn (t'.[2 * i' + 1 + 1] <? t'.[2 * i' + 1]) Ec; cost_simpl | ];
        zl swap_cost 2%nat; gen_swap; cbn_w;
      match goal with |- context [(i' <? ?C)%uint63] =>
        zero_if (i' <? C);
        repeat match goal with |- context [@cost ?T ?X] =>
          lazymatch X with bdec_cost stepsCM ?b ?w => gen_with T X (bdec_time b w) end end;
        cost_destruct (bdec ((i' <? C) && (C <? s))); cost_simpl; [| lia ];
        cost_destruct (t'.[C] <? t'.[i']); cost_simpl; [| lia];
        let e' := fresh "e'" in pose proof e as e'; apply andb_prop in e'; destruct e' as [_ e']; rewrite ltb_spec in e';
        match goal with |- context [@cost ?T (?G' ?t2 ?tc2 s sC C ?w ?h ?e2)] =>
          gen_with T (G' t2 tc2 s sC C w h e2) (IH t2 tc2 C w h e2 ltac:(nia) ltac:(lia)) end;
        lia
      end. }
  match goal with |- context [@cost ?T (?G t tC s sC i iC H HC)] =>
    exact (HG _ t tC i iC H HC Hk Hb : (@cost T (G t tC s sC i iC H HC) <= _)%nat) end.
Qed.


Section CostG.
Variables (n : int) (us vs ws : array int).
Hypothesis Hn : (1 <= N n <= 150)%Z.
Hypothesis HM : (M us <= 5000)%Z.
Hypothesis Hlv : PArray.length vs = PArray.length us.
Hypothesis Hlw : PArray.length ws = PArray.length us.
Hypothesis Hend : forall k, (0 <= k < M us)%Z -> (0 <= au us k < N n /\ 0 <= av vs k < N n)%Z.
Hypothesis Hwt : forall k, (0 <= k < M us)%Z -> (-1000 <= aw ws k <= 1000)%Z.

Lemma chain_acc_time (nx : array int) nxC
  (Hnx : forall e, (0 <= e < M us)%Z -> at_ nx e = Lb us (au us e) e)
  S SC f fC (x : Z) (Inv : Z -> S -> Prop) (K : nat) :
  (forall c (e : int) eC s sC, (0 <= φ e < c)%Z -> (c <= M us)%Z -> Lb us x c = (φ e + 1)%Z -> Inv c s ->
     (cost (fC e eC) + cost (extract (fC e eC) s sC) <= K)%nat /\ Inv (φ e) (f e s)) ->
  forall cur curC c s sC H HC, (0 <= c <= M us)%Z -> φ cur = Lb us x c -> Inv c s ->
  (cost (extract (extract (extract (extract (extract (chain_acc_cost stepsCM S SC) nx nxC) f fC) cur curC) s sC) H HC)
    <= (K + 40) * Z.to_nat (cnt us x c) + 20)%nat.
Proof.
  intros HK cur curC c s sC H HC Hc Hcur HI.
  unfold chain_acc_cost. cbn.
  match goal with |- context [@cost ?T (?G cur curC s sC H HC)] =>
    assert (HG : forall k cur curC c s sC H HC, (Z.to_nat (cnt us x c) <= k)%nat ->
       (0 <= c <= M us)%Z -> φ cur = Lb us x c -> Inv c s ->
       (cost (G cur curC s sC H HC) <= (K + 40) * k + 20)%nat) end.
  { induction k as [|k IH]; intros cur' curC' c' s' sC' [g] HC' Hk Hc' Hcur' HI';
      cost_simpl;
      pose proof (bdec_time (0 <? cur') (bool_w (0 <? cur'))) as HB;
      cost_destruct (bdec (0 <? cur')); cost_simpl.
    - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e) as Hlt. change (φ 0) with 0%Z in Hlt.
      destruct (Lb_props us vs ws Hlv Hlw x c' ltac:(lia)) as (L1 & L2 & L3).
      pose proof (cnt_Lb us vs ws Hlv Hlw x c' (Lb us x c' - 1) ltac:(lia) ltac:(lia) ltac:(lia)) as E.
      pose proof (cnt_nonneg us vs ws Hlv Hlw x (Lb us x c' - 1)). lia.
    - lia.
    - pose proof (proj1 (Uint63.ltb_spec _ _) e) as Hlt. change (φ 0) with 0%Z in Hlt.
      destruct (Lb_props us vs ws Hlv Hlw x c' ltac:(lia)) as (L1 & L2 & L3).
      set (e0 := (Lb us x c' - 1)%Z) in *.
      destruct (L2 e0 ltac:(unfold e0; lia) ltac:(unfold e0; lia)) as (A1 & A2 & A3).
      assert (Ee : φ (cur' - 1) = e0) by (unfold e0; zify; lia).
      pose proof (cnt_Lb us vs ws Hlv Hlw x c' e0 ltac:(lia) ltac:(lia) ltac:(lia)) as Ecnt.
      destruct (HK c' (cur' - 1) (int_val stepsCM (cur' - 1)) s' sC' ltac:(lia) ltac:(lia) ltac:(lia) HI') as [HK1 HI2].
      cost_align HK1.
      assert (Hc0 : φ (nx.[cur' - 1]) = Lb us x e0).
      { rewrite <- (at_phi nx (cur' - 1)), Ee, Hnx by lia. rewrite A1. reflexivity. }
      pose proof (bdec_time (nx.[cur' - 1] <? cur') (bool_w (nx.[cur' - 1] <? cur'))) as HB2.
      cost_destruct (bdec (nx.[cur' - 1] <? cur')); cost_simpl.
      + destruct (Lb_props us vs ws Hlv Hlw x e0 ltac:(lia)) as (B1 & _ & _).
        rewrite Ee in HI2.
        match goal with |- context [@cost ?T (?G' (nx.[cur' - 1]) ?w ?s2 ?sc2 ?h ?e2)] =>
          pose proof (IH (nx.[cur' - 1]) w e0 s2 sc2 h e2 ltac:(lia) ltac:(lia) Hc0 HI2 : (@cost T (G' (nx.[cur' - 1]) w s2 sc2 h e2) <= _)%nat) as HIH end.
        lia.
      + lia.
    - lia. }
  match goal with |- context [@cost ?T (?G cur curC s sC H HC)] =>
    exact (HG _ cur curC c s sC H HC (le_n _) Hc Hcur HI : (@cost T (G cur curC s sC H HC) <= _)%nat) end.
Qed.
End CostG.

(* ---- cbase2.v ---- *)
Lemma hpush_time k t tC s sC x xC : (φ s < 2 ^ Z.of_nat k)%Z ->
  (cost (extract (extract (hpush_cost stepsCM t tC) s sC) x xC) <= k * 80 + 40)%nat.
Proof.
  intros Hk. match goal with |- (_ <= ?r)%nat => remember r as RHS eqn:ER end.
  unfold hpush_cost. cost_simpl. zl set_cost 3%nat. ztop set_cost 3%nat. zl sift_up_cost 2%nat.
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with extract (extract (sift_up_cost stepsCM ?t ?tC) ?i ?iC) ?h ?hc =>
      gen_with T X (sift_up_time k t tC i iC h hc Hk) end end.
  subst RHS. lia.
Qed.

Lemma hpop_time k t tC s sC : (0 < φ s <= 2 ^ 40)%Z -> (φ s < 2 ^ Z.of_nat k)%Z ->
  (cost (extract (hpop_cost stepsCM t tC) s sC) <= k * 100 + 80)%nat.
Proof.
  intros Hs Hk. match goal with |- (_ <= ?r)%nat => remember r as RHS eqn:ER end.
  unfold hpop_cost. cost_simpl. zl set_cost 3%nat. ztop set_cost 3%nat. zl sift_down_cost 3%nat.
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with extract (extract (extract (sift_down_cost stepsCM ?t ?tC) ?s ?sC) ?i ?iC) ?h ?hc =>
      gen_with T X (sift_down_time k t tC s sC i iC h hc ltac:(change (φ 0) with 0%Z; zify; lia) ltac:(change (φ 0) with 0%Z; zify; lia)) end end.
  subst RHS. lia.
Qed.

Ltac gen_elems := repeat match goal with |- context [array_elems ?aC ?i] => generalize (array_elems aC i); intro end.
Ltac cell_split := gen_elems; match goal with w : bool_cost stepsCM ?b |- _ =>
  lazymatch b with true => fail | false => fail | _ => cost_destruct b end end.
Ltac sets := zl set_cost 3%nat; ztop set_cost 3%nat; zl make_cost 2%nat; ztop make_cost 2%nat.

Ltac split1 := gen_elems; first [ cell_split | match goal with |- context [bool_cost stepsCM ?b] =>
  lazymatch b with true => fail | false => fail | _ => cost_destruct b end end
  | match goal with |- context [bool_w ?b] =>
  lazymatch b with true => fail | false => fail | _ => cost_destruct b end end ]; cost_simpl.
Ltac split_ifs := repeat split1; sets.

Lemma bfs_visit_time vs vsC e eC st stC :
  (cost (extract (extract (bfs_visit_cost stepsCM vs vsC) e eC) st stC) <= 30)%nat.
Proof.
  destruct stC as [mq mqC tl tlC]. destruct mqC as [mark markC q qC].
  unfold bfs_visit_cost. cost_simpl. cell_split; cost_simpl; sets; lia.
Qed.

Lemma seed_step_time seed seedC a aC st stC :
  (cost (extract (extract (seed_step_cost stepsCM seed seedC) a aC) st stC) <= 30)%nat.
Proof.
  destruct stC as [mq mqC tl tlC]. destruct mqC as [mark markC q qC].
  unfold seed_step_cost. cost_simpl. cell_split; cost_simpl; sets; lia.
Qed.

Lemma copy_step_time n nC s sC row rowC v vC r rC :
  (cost (extract (extract (extract (extract (copy_step_cost stepsCM n nC) s sC) row rowC) v vC) r rC) <= 30)%nat.
Proof. unfold copy_step_cost. cost_simpl. sets. lia. Qed.

Lemma bf_edge_time us usC vs vsC ws wsC keep keepC (Kk : nat) k kC h hC :
  (forall k kC, cost (keepC k kC) <= Kk)%nat ->
  (cost (extract (extract (extract (extract (extract (bf_edge_cost stepsCM us usC) vs vsC) ws wsC) keep keepC) k kC) h hC) <= Kk + 40)%nat.
Proof.
  intros HK. pose proof (HK k kC) as HK1.
  unfold bf_edge_cost. cost_simpl. revert HK1; generalize (cost (keepC k kC)); intros ck HK1.
  split_ifs; lia.
Qed.

Lemma bad_step_time n nC us usC vs vsC ws wsC R RC h hC k kC b bC :
  (cost (extract (extract (extract (extract (extract (extract (extract (bad_step_cost stepsCM n nC) us usC) vs vsC) ws wsC) R RC) h hC) k kC) b bC) <= 60)%nat.
Proof.
  unfold bad_step_cost. cost_simpl. split_ifs; lia.
Qed.

Lemma negseed_step_time n nC R RC bd bdC u uC a aC s sC :
  (cost (extract (extract (extract (extract (extract (negseed_step_cost stepsCM n nC) R RC) bd bdC) u uC) a aC) s sC) <= 40)%nat.
Proof.
  unfold negseed_step_cost. cost_simpl. split_ifs; lia.
Qed.

Lemma cell_time n nC R RC neg negC D DC p pC u uC v vC :
  (cost (extract (extract (extract (extract (extract (extract (cell_cost stepsCM n nC) R RC) neg negC) D DC) p pC) u uC) v vC) <= 40)%nat.
Proof.
  unfold cell_cost. cost_simpl. split_ifs; lia.
Qed.

Ltac gen_hpush := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (hpush_cost stepsCM ?t ?tC) ?s ?sC) ?x ?xC =>
    gen_with T X (hpush_time _ t tC s sC x xC ltac:(eassumption)) end end.

Lemma relax_time k vs vsC ws wsC bd bdC dn dnC p pC v vC d dC e eC st stC :
  (φ (snd st) < 2 ^ Z.of_nat k)%Z ->
  (cost (extract (extract (extract (extract (extract (extract (extract (extract (relax_cost stepsCM vs vsC) ws wsC) bd bdC) dn dnC) p pC) v vC) d dC) e eC) st stC) <= k * 80 + 150)%nat.
Proof.
  destruct stC as [Dh DhC sz szC]. destruct DhC as [D DC hp hpC]. cbn [snd]. intros Hk.
  match goal with |- (_ <= ?r)%nat => remember r as RHS eqn:ER end.
  unfold relax_cost. cost_simpl. zl hpush_cost 2%nat. split_ifs; gen_hpush; subst RHS; lia.
Qed.

Ltac gen_for_loop K HK := match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (for_loop_cost stepsCM ?S ?SC) ?f ?fC) ?lo ?loC) ?hi ?hiC) ?s ?sC =>
    pose proof (for_loop_time S SC f fC K HK lo loC hi hiC s sC) end end.

Lemma bf_round_time m mC us usC vs vsC ws wsC keep keepC (Kk : nat) r rC h hC :
  (forall k kC, cost (keepC k kC) <= Kk)%nat ->
  (cost (extract (extract (extract (extract (extract (extract (bf_round_cost stepsCM m mC) us usC) vs vsC) ws wsC) keep keepC) r rC) h hC)
    <= (Kk + 60) * Z.to_nat (φ m) + 40)%nat.
Proof.
  intros HKk. match goal with |- (_ <= ?r)%nat => remember r as RHS eqn:ER end.
  unfold bf_round_cost. cost_simpl. zl for_loop_cost 4%nat. zl bf_edge_cost 5%nat.
  assert (HK : forall i iC s0 sC0, (cost (extract (extract (extract (extract (bf_edge_cost stepsCM us usC) vs vsC) ws wsC) keep keepC) i iC) +
      cost (extract (extract (extract (extract (extract (bf_edge_cost stepsCM us usC) vs vsC) ws wsC) keep keepC) i iC) s0 sC0) <= Kk + 40)%nat).
  { intros i iC s0 sC0. change (cost (extract (extract (extract (extract (bf_edge_cost stepsCM us usC) vs vsC) ws wsC) keep keepC) i iC)) with 0%nat.
    apply bf_edge_time. exact HKk. }
  gen_for_loop (Kk + 40)%nat HK.
  subst RHS. unfold gap in *. change (φ 0) with 0%Z in *. rewrite Z.sub_0_r in *. lia.
Qed.

Lemma bf_time n nC m mC us usC vs vsC ws wsC keep keepC (Kk : nat) :
  (forall k kC, cost (keepC k kC) <= Kk)%nat ->
  (cost (extract (extract (extract (extract (extract (bf_cost stepsCM n nC) m mC) us usC) vs vsC) ws wsC) keep keepC)
    <= Z.to_nat (φ n) * ((Kk + 60) * Z.to_nat (φ m) + 60) + 40)%nat.
Proof.
  intros HKk. match goal with |- (_ <= ?r)%nat => remember r as RHS eqn:ER end.
  unfold bf_cost. cost_simpl. sets. zl for_loop_cost 4%nat. zl bf_round_cost 5%nat.
  assert (HK : forall i iC s0 sC0, (cost (extract (extract (extract (extract (extract (bf_round_cost stepsCM m mC) us usC) vs vsC) ws wsC) keep keepC) i iC) +
      cost (extract (extract (extract (extract (extract (extract (bf_round_cost stepsCM m mC) us usC) vs vsC) ws wsC) keep keepC) i iC) s0 sC0) <= (Kk + 60) * Z.to_nat (φ m) + 40)%nat).
  { intros i iC s0 sC0. change (cost (extract (extract (extract (extract (extract (bf_round_cost stepsCM m mC) us usC) vs vsC) ws wsC) keep keepC) i iC)) with 0%nat.
    apply bf_round_time. exact HKk. }
  gen_for_loop ((Kk + 60) * Z.to_nat (φ m) + 40)%nat HK.
  subst RHS. unfold gap in *. change (φ 0) with 0%Z in *. rewrite Z.sub_0_r in *. lia.
Qed.

Section CostG2.
Variables (n : int) (us vs ws : array int).
Hypothesis Hn : (1 <= N n <= 150)%Z.
Hypothesis HM : (M us <= 5000)%Z.
Hypothesis Hlv : PArray.length vs = PArray.length us.
Hypothesis Hlw : PArray.length ws = PArray.length us.
Hypothesis Hend : forall k, (0 <= k < M us)%Z -> (0 <= au us k < N n /\ 0 <= av vs k < N n)%Z.
Hypothesis Hwt : forall k, (0 <= k < M us)%Z -> (-1000 <= aw ws k <= 1000)%Z.

Fixpoint qwc (q : array int) (h : Z) (k : nat) : Z :=
  match k with O => 0%Z | S k' => (cnt us (at_ q h) (M us) + qwc q (h + 1) k')%Z end.
Definition QW (q : array int) (h tl : Z) : Z := qwc q h (Z.to_nat (tl - h)).

Lemma qwc_nonneg q h k : (0 <= qwc q h k)%Z.
Proof.
  revert h; induction k as [|k IH]; intros h; cbn [qwc]; [lia|].
  pose proof (cnt_nonneg us vs ws Hlv Hlw (at_ q h) (M us)). specialize (IH (h + 1)%Z). lia.
Qed.

Lemma qwc_ext q q' h k : (forall j, (h <= j < h + Z.of_nat k)%Z -> at_ q' j = at_ q j) ->
  qwc q' h k = qwc q h k.
Proof.
  revert h; induction k as [|k IH]; intros h E; cbn [qwc]; [reflexivity|].
  rewrite E by lia. rewrite IH; [reflexivity|]. intros j Hj. apply E. lia.
Qed.

Lemma qwc_snoc q h k : qwc q h (S k) = (qwc q h k + cnt us (at_ q (h + Z.of_nat k)) (M us))%Z.
Proof.
  revert h; induction k as [|k IH]; intros h; cbn [qwc].
  - replace (h + Z.of_nat 0)%Z with h by lia. cbn [qwc]. lia.
  - cbn [qwc] in IH. rewrite IH. replace (h + 1 + Z.of_nat k)%Z with (h + Z.of_nat (S k))%Z by lia. lia.
Qed.

Lemma QW_pop q h tl : (h < tl)%Z -> QW q h tl = (cnt us (at_ q h) (M us) + QW q (h + 1) tl)%Z.
Proof.
  intros H. unfold QW. replace (Z.to_nat (tl - h)) with (S (Z.to_nat (tl - (h + 1)))) by lia.
  reflexivity.
Qed.

Lemma QW_push q q' h tl b : (h <= tl)%Z ->
  (forall j, (h <= j < tl)%Z -> at_ q' j = at_ q j) -> at_ q' tl = b ->
  QW q' h (tl + 1) = (QW q h tl + cnt us b (M us))%Z.
Proof.
  intros H E Eb. unfold QW. replace (Z.to_nat (tl + 1 - h)) with (S (Z.to_nat (tl - h))) by lia.
  rewrite qwc_snoc. rewrite (qwc_ext q q') by (intros j Hj; apply E; lia).
  replace (h + Z.of_nat (Z.to_nat (tl - h)))%Z with tl by lia. rewrite Eb. reflexivity.
Qed.

Lemma QW_nonneg q h tl : (0 <= QW q h tl)%Z.
Proof. apply qwc_nonneg. Qed.

Definition bpot (mark : array bool) (q : array int) (h tl : Z) : Z :=
  (remc us mark (Z.to_nat (M us)) + QW q h tl)%Z.

Definition bst (h0 R : Z) (st : array bool * array int * int) : Prop :=
  let '(mark, q, tl) := st in
  binv n (fun _ => True) mark q tl /\ (0 <= h0 <= φ tl)%Z /\ bpot mark q h0 (φ tl) = R.

Lemma bpot_nonneg mark q h tl : (0 <= bpot mark q h tl)%Z.
Proof. unfold bpot. pose proof (remc_bound us vs ws Hlv Hlw mark (Z.to_nat (M us))). pose proof (QW_nonneg q h tl). lia. Qed.

Lemma push_pot mark q tl (b : int) h0 :
  binv n (fun _ => True) mark q tl -> (0 <= h0 <= φ tl)%Z -> (0 <= φ b < N n)%Z -> atb mark (φ b) = false ->
  binv n (fun _ => True) (mark.[b <- true]) (q.[tl <- b]) (tl + 1) /\ (0 <= h0 <= φ (tl + 1))%Z /\
  bpot (mark.[b <- true]) (q.[tl <- b]) h0 (φ (tl + 1)) = bpot mark q h0 (φ tl).
Proof.
  intros BI Hh Hb Hm.
  destruct (push_spec n us vs ws Hn Hlv Hlw (fun _ => True) mark q tl b BI ltac:(lia) Hm I) as (BI' & _ & _).
  pose proof (bi_tl _ _ _ _ _ BI') as T'. pose proof (bi_lq _ _ _ _ _ BI) as LQ. pose proof (bi_lm _ _ _ _ _ BI) as LM.
  pose proof (bi_tl _ _ _ _ _ BI) as T.
  pose proof (N_wB n us vs ws Hn Hlv Hlw) as NW.
  assert (Et : φ (tl + 1) = (φ tl + 1)%Z) by (apply phi_add1; rewrite wB_val in NW; lia).
  rewrite Et in T'.
  split; [exact BI' | split; [lia |]].
  unfold bpot. rewrite Et.
  rewrite (remc_set n us vs ws Hn Hlv Hlw Hend mark b) by (auto; lia).
  rewrite (QW_push q (q.[tl <- b]) h0 (φ tl) (φ b)); [| lia | |].
  - unfold cnt. lia.
  - intros j Hj. rewrite at_set; [| rewrite LQ; unfold N in *; lia | rewrite wB_val; lia].
    destruct (Z.eqb_spec j (φ tl)); [lia | reflexivity].
  - rewrite at_set; [| rewrite LQ; unfold N in *; lia | rewrite wB_val; lia]. rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma visit_pot h0 R (e : int) st : (0 <= φ e < M us)%Z -> bst h0 R st -> bst h0 R (bfs_visit vs e st).
Proof.
  intros He. destruct st as [[mark q] tl]. intros (BI & Hh & HR). unfold bfs_visit.
  assert (Hb : (0 <= φ (vs.[e]) < N n)%Z) by (rewrite <- (av_phi vs e); apply Hend; lia).
  destruct (mark.[vs.[e]]) eqn:Em; [split; auto|].
  rewrite <- (atb_phi mark) in Em.
  destruct (push_pot mark q tl (vs.[e]) h0 BI Hh Hb Em) as (A1 & A2 & A3).
  split; [exact A1 | split; [exact A2 | rewrite A3; exact HR]].
Qed.

Lemma chain_bst nx (Hnx : forall e, (0 <= e < M us)%Z -> at_ nx e = Lb us (au us e) e) x h0 R cur c st :
  (0 <= c <= M us)%Z -> φ cur = Lb us x c -> bst h0 R st -> bst h0 R (chain_fold nx (bfs_visit vs) cur st).
Proof.
  intros Hc Hcur HI.
  destruct (chain_spec us vs ws HM Hlv Hlw nx (bfs_visit vs) x (fun _ s => bst h0 R s) Hnx) with (cur := cur) (c := c) (s := st)
    as (c' & _ & _ & HR); auto.
  intros c0 e s0 He Hc0 _ Hs0. apply visit_pot; [| exact Hs0].
  pose proof (M_wB us vs ws HM Hlv Hlw). rewrite of_Z_phi; [lia | rewrite wB_val; lia].
Qed.

Lemma binv_init : binv n (fun _ => True) (PArray.make n false) (PArray.make n 0) 0.
Proof.
  unfold N in Hn. split.
  - apply alen_make_b. lia.
  - apply alen_make_i. lia.
  - change (φ 0) with 0%Z. unfold N. lia.
  - intros y Hy. rewrite atb_make. change (φ 0) with 0%Z. split; [discriminate | intros (j & Hj & _); lia].
  - intros j Hj. change (φ 0) with 0%Z in Hj. lia.
  - intros i j Hi. change (φ 0) with 0%Z in Hi. lia.
  - intros; exact I.
Qed.

Lemma seed_bst seed :
  bst 0 (M us) (for_loop (seed_step seed) 0 n (PArray.make n false, PArray.make n 0, 0)).
Proof.
  set (Inv := fun (a : Z) (st : array bool * array int * int) =>
    bst 0 (M us) st /\ let '(mark, q, tl) := st in forall y, (0 <= y < N n)%Z -> atb mark y = true -> (y < a)%Z).
  enough (H : Inv (φ n) (for_loop (seed_step seed) 0 n (PArray.make n false, PArray.make n 0, 0))) by apply H.
  pose proof (N_wB n us vs ws Hn Hlv Hlw) as NW. rewrite wB_val in NW.
  pose proof (M_nonneg us vs ws Hlv Hlw) as M0.
  apply for_loop_inv; change (φ 0) with 0%Z; [unfold N in Hn; lia | |].
  - split; [split; [apply binv_init | split; [change (φ 0) with 0%Z; lia |]] |].
    + unfold bpot, QW. rewrite (remc_all n us vs ws Hlv Hlw). change (φ 0) with 0%Z. replace (Z.to_nat (0 - 0)) with O by reflexivity. cbn [qwc]. lia.
    + intros y Hy. rewrite atb_make. discriminate.
  - intros a [[mark q] tl] Ha [HB HY]. unfold seed_step.
    destruct (seed.[a]) eqn:Es.
    + destruct HB as (BI & Hh & HR).
      assert (Hm : atb mark (φ a) = false) by (destruct (atb mark (φ a)) eqn:E; [specialize (HY (φ a) ltac:(unfold N in *; lia) E); lia | reflexivity]).
      destruct (push_pot mark q tl a 0 BI Hh ltac:(unfold N in *; lia) Hm) as (A1 & A2 & A3).
      split; [split; [exact A1 | split; [exact A2 | rewrite A3; exact HR]] |].
      intros y Hy E. rewrite atb_set in E; [| rewrite (bi_lm _ _ _ _ _ BI); unfold N in *; lia | lia].
      destruct (Z.eqb_spec y (φ a)); [lia | specialize (HY y Hy E); lia].
    + split; [exact HB |]. intros y Hy E. specialize (HY y Hy E). lia.
Qed.

Lemma chain_fold_time nx nxC (Hnx : forall e, (0 <= e < M us)%Z -> at_ nx e = Lb us (au us e) e)
  S SC f fC (x : Z) (Inv : Z -> S -> Prop) (K : nat) :
  (forall c (e : int) eC s sC, (0 <= φ e < c)%Z -> (c <= M us)%Z -> Lb us x c = (φ e + 1)%Z -> Inv c s ->
     (cost (fC e eC) + cost (extract (fC e eC) s sC) <= K)%nat /\ Inv (φ e) (f e s)) ->
  forall cur curC c s sC, (0 <= c <= M us)%Z -> φ cur = Lb us x c -> Inv c s ->
  (cost (extract (extract (extract (extract (chain_fold_cost stepsCM S SC) nx nxC) f fC) cur curC) s sC)
    <= (K + 40) * Z.to_nat (cnt us x c) + 40)%nat.
Proof.
  intros HK cur curC c s sC Hc Hcur HI.
  refine (Nat.le_trans _ _ _ (chain_fold_time_gen S SC nx nxC f fC cur curC s sC ((K + 40) * Z.to_nat (cnt us x c) + 20) _) _); [| lia].
  intros H HC. exact (chain_acc_time us vs ws HM Hlv Hlw nx nxC Hnx S SC f fC x Inv K HK cur curC c s sC H HC Hc Hcur HI).
Qed.

Lemma bfs_visit_layer vs0 vsC e eC : cost (extract (bfs_visit_cost stepsCM vs0 vsC) e eC) = 0%nat.
Proof. reflexivity. Qed.

Lemma bfs_acc_time hd hdC nx nxC vsC nC
  (Hhd : forall a, (0 <= a < N n)%Z -> at_ hd a = Lb us a (M us))
  (Hnx : forall e, (0 <= e < M us)%Z -> at_ nx e = Lb us (au us e) e) :
  forall k h hC st stC H HC R, (Z.to_nat (gap n h) <= k)%nat -> bst (φ h) R st ->
  (cost (extract (extract (extract (extract (extract (extract (bfs_acc_cost stepsCM hd hdC) nx nxC) vs vsC) n nC) h hC) st stC) H HC)
    <= k * 200 + Z.to_nat R * 80 + 30)%nat.
Proof.
  intros k0 h hC st stC H HC R Hk HI.
  unfold bfs_acc_cost. cbn.
  match goal with |- context [@cost ?T (?G hd hdC nx nxC vs vsC n nC h hC st stC H HC)] =>
    assert (HG : forall k h hC st stC H HC R, (Z.to_nat (gap n h) <= k)%nat -> bst (φ h) R st ->
       (cost (G hd hdC nx nxC vs vsC n nC h hC st stC H HC) <= k * 200 + Z.to_nat R * 80 + 30)%nat) end.
  { induction k as [|k IH]; intros h' hC' st' stC' [g] HC' R' Hk' HI';
      destruct stC' as [mq mqC tl tlC]; destruct mqC as [mark markC q qC];
      cost_simpl_h bfs_acc;
      zero_if (h' <? tl);
      repeat match goal with |- context [@cost ?T ?X] =>
        lazymatch X with bdec_cost stepsCM ?b ?w => gen_with T X (bdec_time b w) end end;
      cost_destruct (bdec ((h' <? tl) && (h' <? n))); cost_simpl; [| lia | | lia].
    - exfalso. pose proof e as e'. apply andb_prop in e'. destruct e' as [_ e']. rewrite ltb_spec in e'. unfold gap in Hk'. lia.
    - pose proof e as e'. apply andb_prop in e'. destruct e' as [E1 E2]. rewrite ltb_spec in E1, E2.
      destruct HI' as (BI & Hh & HR).
      pose proof (bi_qb _ _ _ _ _ BI (φ h') ltac:(lia)) as Hq. rewrite at_phi in Hq.
      assert (Hcur : φ (hd.[q.[h']]) = Lb us (φ (q.[h'])) (M us)) by (rewrite <- at_phi; apply Hhd; lia).
      pose proof (M_nonneg us vs ws Hlv Hlw) as M0.
      zl bfs_visit_cost 2%nat. zl chain_fold_cost 4%nat.
      match goal with |- context [@cost ?T ?X] =>
        lazymatch X with extract (extract (extract (extract (chain_fold_cost stepsCM ?S ?SC) nx ?nxC') ?f ?fC) ?cur ?curC) ?s ?sC =>
          gen_with T X (chain_fold_time nx nxC' Hnx S SC f fC (φ (q.[h'])) (fun _ _ => True) 30
             ltac:(intros c0 e0 eC0 s0 sC0 _ _ _ _; split; [| exact I];
                   refine (Nat.le_trans _ _ _ (Nat.add_le_mono _ _ _ _ (Nat.eq_le_incl _ _ (bfs_visit_layer vs vsC e0 eC0)) (bfs_visit_time vs vsC e0 eC0 s0 sC0)) _); lia)
             cur curC (M us) s sC ltac:(lia) Hcur I) end end.
      pose proof (cnt_nonneg us vs ws Hlv Hlw (φ (q.[h'])) (M us)) as C0.
      assert (HI2 : bst (φ (h' + 1)) (R' - cnt us (φ (q.[h'])) (M us)) (chain_fold nx (bfs_visit vs) hd.[q.[h']] (mark, q, tl))).
      { apply (chain_bst nx Hnx (φ (q.[h'])) _ _ _ (M us)); [lia | exact Hcur |].
        assert (Eh : φ (h' + 1) = (φ h' + 1)%Z) by (apply phi_add1; unfold N in *; lia).
        split; [exact BI | split; [lia |]]. rewrite <- HR. unfold bpot. rewrite Eh, (QW_pop q (φ h') (φ tl)) by lia.
        rewrite at_phi. lia. }
      assert (Hk2 : (Z.to_nat (gap n (h' + 1)) <= k)%nat).
      { assert (Eh : φ (h' + 1) = (φ h' + 1)%Z) by (apply phi_add1; unfold N in *; lia). unfold gap in *. lia. }
      assert (R2 : (0 <= R' - cnt us (φ (q.[h'])) (M us))%Z).
      { clear -HI2 Hlv Hlw. revert HI2. generalize (chain_fold nx (bfs_visit vs) hd.[q.[h']] (mark, q, tl)).
        intros [[m2 q2] t2] (_ & _ & H3). rewrite <- H3. apply bpot_nonneg. }
      match goal with |- context [@cost ?T (F hd hdC nx nxC vs vsC n nC (h' + 1)%uint63 ?w ?st2 ?stc2 ?hh ?ee)] =>
        gen_with T (F hd hdC nx nxC vs vsC n nC (h' + 1)%uint63 w st2 stc2 hh ee) (IH (h' + 1)%uint63 w st2 stc2 hh ee _ Hk2 HI2) end.
      lia. }
  match goal with |- context [@cost ?T (?G hd hdC nx nxC vs vsC n nC h hC st stC H HC)] =>
    exact (HG _ h hC st stC H HC R Hk HI : (@cost T (G hd hdC nx nxC vs vsC n nC h hC st stC H HC) <= _)%nat) end.
Qed.

Lemma seed_step_layer seed seedC a aC : cost (extract (seed_step_cost stepsCM seed seedC) a aC) = 0%nat.
Proof. reflexivity. Qed.


Lemma closure_time hd hdC nx nxC vsC nC seed seedC
  (Hhd : forall a, (0 <= a < N n)%Z -> at_ hd a = Lb us a (M us))
  (Hnx : forall e, (0 <= e < M us)%Z -> at_ nx e = Lb us (au us e) e) :
  (cost (extract (extract (extract (extract (closure_cost stepsCM n nC) hd hdC) nx nxC) vs vsC) seed seedC)
    <= Z.to_nat (N n) * 300 + Z.to_nat (M us) * 80 + 200)%nat.
Proof.
  match goal with |- (_ <= ?r)%nat => remember r as RHS eqn:ER end.
  unfold closure_cost. cost_simpl. sets. zl for_loop_cost 4%nat. zl seed_step_cost 1%nat. zl bfs_acc_cost 6%nat.
  assert (HKs : forall i iC s0 sC0, (cost (extract (seed_step_cost stepsCM seed seedC) i iC) + cost (extract (extract (seed_step_cost stepsCM seed seedC) i iC) s0 sC0) <= 30)%nat).
  { intros i iC s0 sC0; refine (Nat.le_trans _ _ _ (Nat.add_le_mono _ _ _ _ (Nat.eq_le_incl _ _ (seed_step_layer seed seedC i iC)) (seed_step_time seed seedC i iC s0 sC0)) _); lia. }
  gen_for_loop 30%nat HKs.
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with extract (extract (extract (extract (extract (extract (bfs_acc_cost stepsCM hd ?hdC') nx ?nxC') vs ?vsC') n ?nC') ?h ?hC) ?st ?stC) ?H ?HC =>
      gen_with T X (bfs_acc_time hd hdC' nx nxC' vsC' nC' Hhd Hnx _ h hC st stC H HC (M us) (le_n _) (seed_bst seed)) end end.
  subst RHS. unfold gap in *. change (φ 0) with 0%Z in *. rewrite Z.sub_0_r in *. unfold N. lia.
Qed.

Lemma copy_step_layer n0 nC s sC row rowC v vC :
  cost (extract (extract (extract (copy_step_cost stepsCM n0 nC) s sC) row rowC) v vC) = 0%nat.
Proof. reflexivity. Qed.

Lemma reach_row_time hd hdC nx nxC vsC nC s sC r rC
  (Hhd : forall a, (0 <= a < N n)%Z -> at_ hd a = Lb us a (M us))
  (Hnx : forall e, (0 <= e < M us)%Z -> at_ nx e = Lb us (au us e) e) :
  (cost (extract (extract (extract (extract (extract (reach_row_cost stepsCM n nC) hd hdC) nx nxC) vs vsC) s sC) r rC)
    <= Z.to_nat (N n) * 350 + Z.to_nat (M us) * 80 + 300)%nat.
Proof.
  match goal with |- (_ <= ?r)%nat => remember r as RHS eqn:ER end.
  unfold reach_row_cost. cost_simpl. sets. zl for_loop_cost 4%nat. zl copy_step_cost 3%nat. zl closure_cost 4%nat.
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with extract (extract (extract (extract (closure_cost stepsCM n ?nC') hd ?hdC') nx ?nxC') vs ?vsC') ?sd ?sdC =>
      pose proof (closure_time hd hdC' nx nxC' vsC' nC' sd sdC Hhd Hnx) end end.
  match goal with |- context [extract (extract (copy_step_cost stepsCM n ?nC') s ?sC') ?row ?rowC] =>
  assert (HK : forall i iC s0 sC0, (cost (extract (extract (extract (copy_step_cost stepsCM n nC') s sC') row rowC) i iC) +
      cost (extract (extract (extract (extract (copy_step_cost stepsCM n nC') s sC') row rowC) i iC) s0 sC0) <= 30)%nat)
  by (intros i iC s0 sC0; rewrite copy_step_layer; apply copy_step_time) end.
  gen_for_loop 30%nat HK.
  subst RHS. unfold gap in *. change (φ 0) with 0%Z in *. rewrite Z.sub_0_r in *. unfold N in *. lia.
Qed.

Lemma reach_matrix_time hd hdC nx nxC vsC nC
  (Hhd : forall a, (0 <= a < N n)%Z -> at_ hd a = Lb us a (M us))
  (Hnx : forall e, (0 <= e < M us)%Z -> at_ nx e = Lb us (au us e) e) :
  (cost (extract (extract (extract (reach_matrix_cost stepsCM n nC) hd hdC) nx nxC) vs vsC)
    <= Z.to_nat (N n) * (Z.to_nat (N n) * 350 + Z.to_nat (M us) * 80 + 400) + 100)%nat.
Proof.
  match goal with |- (_ <= ?r)%nat => remember r as RHS eqn:ER end.
  unfold reach_matrix_cost. cost_simpl. sets. zl for_loop_cost 4%nat. zl reach_row_cost 4%nat.
  match goal with |- context [extract (extract (extract (reach_row_cost stepsCM n ?nC') hd ?hdC') nx ?nxC') vs ?vsC'] =>
  assert (HK : forall i iC s0 sC0, (cost (extract (extract (extract (extract (reach_row_cost stepsCM n nC') hd hdC') nx nxC') vs vsC') i iC) +
      cost (extract (extract (extract (extract (extract (reach_row_cost stepsCM n nC') hd hdC') nx nxC') vs vsC') i iC) s0 sC0)
      <= Z.to_nat (N n) * 350 + Z.to_nat (M us) * 80 + 300)%nat)
  by (intros i iC s0 sC0; change (cost (extract (extract (extract (extract (reach_row_cost stepsCM n nC') hd hdC') nx nxC') vs vsC') i iC)) with 0%nat;
      apply reach_row_time; assumption) end.
  gen_for_loop (Z.to_nat (N n) * 350 + Z.to_nat (M us) * 80 + 300)%nat HK.
  subst RHS. unfold gap in *. change (φ 0) with 0%Z in *. rewrite Z.sub_0_r in *. unfold N in *. lia.
Qed.

End CostG2.

Section CostDij.
Variables (n : int) (us vs ws : array int).
Hypothesis Hn : (1 <= N n <= 150)%Z.
Hypothesis HM : (M us <= 5000)%Z.
Hypothesis Hlv : PArray.length vs = PArray.length us.
Hypothesis Hlw : PArray.length ws = PArray.length us.
Hypothesis Hend : forall k, (0 <= k < M us)%Z -> (0 <= au us k < N n /\ 0 <= av vs k < N n)%Z.
Hypothesis Hwt : forall k, (0 <= k < M us)%Z -> (-1000 <= aw ws k <= 1000)%Z.
Variables (hd nx : array int).
Hypothesis Hhd : forall a, (0 <= a < N n)%Z -> at_ hd a = Lb us a (M us).
Hypothesis Hnx : forall e, (0 <= e < M us)%Z -> at_ nx e = Lb us (au us e) e.
Variables (bd : array bool) (p : array int).
Hypothesis Hlb : PArray.length bd = n.
Hypothesis Hlp : PArray.length p = n.
Hypothesis Hfeas : forall a b w, Gs us vs ws bd a b w -> (sat p b <= sat p a + w)%Z.
Hypothesis Hpb : forall v, (0 <= v < N n)%Z -> (- 1000 * (N n - 1) <= sat p v <= 0)%Z.
Hypothesis Hshort : forall x y c L, pw (Gs us vs ws bd) x y c L -> (0 <= x < N n)%Z ->
  exists c' L', pw (Gs us vs ws bd) x y c' L' /\ (c' <= c)%Z /\ (Z.of_nat (List.length L') <= N n)%Z.
Variable L : nat.
Hypothesis HL : (M us + 1 < 2 ^ Z.of_nat L)%Z.

Lemma relax_sz dn v d e st : (φ (snd st) < 2 ^ 40)%Z -> (φ (snd (relax vs ws bd dn p v d e st)) <= φ (snd st) + 1)%Z.
Proof.
  destruct st as [[D hp] sz]. cbn [snd]. intros H. unfold relax.
  destruct (negb bd.[vs.[e]] && negb dn.[vs.[e]]); [| cbn [snd]; lia].
  destruct (_ <? _); cbn [snd]; [| lia]. rewrite phi_add1; lia.
Qed.

Lemma relax_layer vsC wsC bdC dn dnC pC v vC d dC e eC :
  cost (extract (extract (extract (extract (extract (extract (extract (relax_cost stepsCM vs vsC) ws wsC) bd bdC) dn dnC) p pC) v vC) d dC) e eC) = 0%nat.
Proof. reflexivity. Qed.

Lemma relax_chain_time nxC vsC wsC bdC dn dnC pC v vC d dC cur curC st stC :
  φ cur = Lb us (φ v) (M us) -> (φ (snd st) + cnt us (φ v) (M us) <= M us + 1)%Z ->
  (cost (extract (extract (extract (extract (chain_fold_cost stepsCM (array int * array int * int)
     (prod_cost stepsCM (array int * array int) (prod_cost stepsCM (array int) (array_cost stepsCM int (int_cost stepsCM))
        (array int) (array_cost stepsCM int (int_cost stepsCM))) int (int_cost stepsCM))) nx nxC)
     (relax vs ws bd dn p v d)
     (extract (extract (extract (extract (extract (extract (extract (relax_cost stepsCM vs vsC) ws wsC) bd bdC) dn dnC) p pC) v vC) d dC)))
     cur curC) st stC) <= (L * 80 + 190) * Z.to_nat (cnt us (φ v) (M us)) + 40)%nat.
Proof.
  intros Hcur Hst. pose proof (M_nonneg us vs ws Hlv Hlw) as M0.
  assert (HL40 : (M us + 1 < 2 ^ 40)%Z) by lia.
  replace (L * 80 + 190)%nat with (L * 80 + 150 + 40)%nat by lia.
  refine (chain_fold_time us vs ws HM Hlv Hlw nx nxC Hnx _ _ _ _ (φ v)
    (fun c s => φ (snd s) + cnt us (φ v) c <= M us + 1)%Z (L * 80 + 150) _ cur curC (M us) st stC ltac:(lia) Hcur Hst).
  intros c e eC s sC He Hc HLb HI.
  pose proof (cnt_Lb us vs ws Hlv Hlw (φ v) c (φ e) ltac:(lia) ltac:(lia) HLb) as Ec.
  pose proof (cnt_nonneg us vs ws Hlv Hlw (φ v) (φ e)) as C0.
  split.
  - eapply Nat.le_trans; [apply Nat.add_le_mono; [apply Nat.eq_le_incl; apply relax_layer | apply (relax_time L); lia] | lia].
  - pose proof (relax_sz dn v d e s ltac:(lia)). lia.
Qed.

End CostDij.

(* ---- cbase3.v ---- *)
Section CostDij.
Variables (n : int) (us vs ws : array int).
Hypothesis Hn : (1 <= N n <= 150)%Z.
Hypothesis HM : (M us <= 5000)%Z.
Hypothesis Hlv : PArray.length vs = PArray.length us.
Hypothesis Hlw : PArray.length ws = PArray.length us.
Hypothesis Hend : forall k, (0 <= k < M us)%Z -> (0 <= au us k < N n /\ 0 <= av vs k < N n)%Z.
Hypothesis Hwt : forall k, (0 <= k < M us)%Z -> (-1000 <= aw ws k <= 1000)%Z.
Variables (hd nx : array int).
Hypothesis Hhd : forall a, (0 <= a < N n)%Z -> at_ hd a = Lb us a (M us).
Hypothesis Hnx : forall e, (0 <= e < M us)%Z -> at_ nx e = Lb us (au us e) e.
Variables (bd : array bool) (p : array int).
Hypothesis Hlb : PArray.length bd = n.
Hypothesis Hlp : PArray.length p = n.
Hypothesis Hfeas : forall a b w, Gs us vs ws bd a b w -> (sat p b <= sat p a + w)%Z.
Hypothesis Hpb : forall v, (0 <= v < N n)%Z -> (- 1000 * (N n - 1) <= sat p v <= 0)%Z.
Hypothesis Hshort : forall x y c L, pw (Gs us vs ws bd) x y c L -> (0 <= x < N n)%Z ->
  exists c' L', pw (Gs us vs ws bd) x y c' L' /\ (c' <= c)%Z /\ (Z.of_nat (List.length L') <= N n)%Z.
Variable L : nat.
Hypothesis HL : (M us + 1 < 2 ^ Z.of_nat L)%Z.

Definition dpot (st : array int * array bool * array int * int) : Z := let '(_, dn, _, _) := st in Rem us dn.
Definition dok (U : Z) (steps : int) (st : array int * array bool * array int * int) : Prop :=
  let '(D, dn, hp, sz) := st in dinv n us vs ws bd p U D dn hp sz steps.

Lemma dij_body_time hdC nxC vsC wsC bdC pC U steps st stC :
  (0 <= U < N n)%Z -> dok U steps st -> (0 < φ (snd st))%Z ->
  (cost (extract (extract (extract (extract (extract (extract (dij_body_cost stepsCM hd hdC) nx nxC) vs vsC) ws wsC) bd bdC) p pC) st stC)
   + Z.to_nat (dpot (dij_body hd nx vs ws bd p st)) * (L * 80 + 200)
   <= L * 100 + 300 + Z.to_nat (dpot st) * (L * 80 + 200))%nat.
Proof.
  destruct stC as [x xC sz szC]. destruct xC as [y yC hp hpC]. destruct yC as [D DC dn dnC].
  cbn [snd]. intros HU DI Hsz. cbn [dok] in DI.
  remember (dpot (dij_body hd nx vs ws bd p (D, dn, hp, sz))) as P2 eqn:EP2.
  change (dpot (D, dn, hp, sz)) with (Rem us dn).
  match goal with |- (_ <= ?r)%nat => remember r as RHS eqn:ER end.
  pose proof (di_count _ _ _ _ _ _ _ _ _ _ _ _ DI) as DC0.
  pose proof (remc_bound us vs ws Hlv Hlw dn (Z.to_nat (M us))) as R0. unfold Rem in DC0.
  pose proof (to_Z_bounded steps) as Bst.
  pose proof (M_nonneg us vs ws Hlv Hlw) as M0.
  unfold dij_body_cost. cost_simpl. zl hpop_cost 1%nat.
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with extract (hpop_cost stepsCM ?t ?tC) ?s ?sC =>
      gen_with T X (hpop_time L t tC s sC ltac:(lia) ltac:(lia)) end end.
  pose proof (di_sound _ _ _ _ _ _ _ _ _ _ _ _ DI 0%Z ltac:(lia)) as [Hv0 _].
  assert (Hv : (0 <= φ (hp.[0] mod 256) < N n)%Z) by (rewrite mod_spec; change (φ 256) with 256%Z; exact Hv0).
  pose proof (di_ldn _ _ _ _ _ _ _ _ _ _ _ _ DI) as Ldn.
  gen_elems. cost_destruct_eqn (dn.[hp.[0] mod 256]) Edv; cost_simpl.
  - (* stale *)
    assert (E2 : P2 = Rem us dn) by (rewrite EP2; unfold dij_body, hpop; cbv zeta; rewrite Edv; reflexivity).
    subst RHS. rewrite E2. lia.
  - gen_elems. cost_destruct_eqn (bd.[hp.[0] mod 256]) Ebv; cost_simpl.
    + sets. assert (ERem : Rem us (dn.[hp.[0] mod 256 <- true]) = (Rem us dn - cnt us (φ (hp.[0] mod 256)) (M us))%Z).
      { unfold Rem, cnt. apply (remc_set n us vs ws Hn Hlv Hlw Hend); [lia | exact Ldn | rewrite atb_phi; exact Edv | lia]. }
      assert (Hge : (cnt us (φ (hp.[0] mod 256)) (M us) <= Rem us dn)%Z).
      { unfold Rem, cnt. apply (remc_ge_cnt us vs ws Hlv Hlw). rewrite atb_phi; exact Edv. }
      pose proof (cnt_nonneg us vs ws Hlv Hlw (φ (hp.[0] mod 256)) (M us)) as C0.
      assert (E2 : P2 = Rem us (dn.[hp.[0] mod 256 <- true])) by (rewrite EP2; unfold dij_body, hpop; cbv zeta; rewrite Edv, Ebv; reflexivity).
      subst RHS. rewrite E2, ERem. lia.
    + sets. zl chain_fold_cost 4%nat. zl relax_cost 7%nat.
      assert (ERem : Rem us (dn.[hp.[0] mod 256 <- true]) = (Rem us dn - cnt us (φ (hp.[0] mod 256)) (M us))%Z).
      { unfold Rem, cnt. apply (remc_set n us vs ws Hn Hlv Hlw Hend); [lia | exact Ldn | rewrite atb_phi; exact Edv | lia]. }
      assert (Hge : (cnt us (φ (hp.[0] mod 256)) (M us) <= Rem us dn)%Z).
      { unfold Rem, cnt. apply (remc_ge_cnt us vs ws Hlv Hlw). rewrite atb_phi; exact Edv. }
      pose proof (cnt_nonneg us vs ws Hlv Hlw (φ (hp.[0] mod 256)) (M us)) as C0.
      assert (E2 : P2 = Rem us (dn.[hp.[0] mod 256 <- true])).
      { rewrite EP2; unfold dij_body, hpop; cbv zeta; rewrite Edv, Ebv.
        destruct (chain_fold _ _ _ _) as [[D2 hp2] sz2]. reflexivity. }
      assert (Hcur : φ (hd.[hp.[0] mod 256]) = Lb us (φ (hp.[0] mod 256)) (M us)) by (rewrite <- at_phi; apply Hhd; lia).
      assert (Hsz1 : φ (sz - 1) = (φ sz - 1)%Z) by (rewrite sub_spec; change (φ 1) with 1%Z; apply Z.mod_small; lia).
      match goal with |- context [@cost ?T ?X] =>
        lazymatch X with extract (extract (extract (extract (chain_fold_cost stepsCM _ _) nx ?nxC') (relax vs ws bd ?dn' p ?v ?d)
             (extract (extract (extract (extract (extract (extract (extract (relax_cost stepsCM vs ?vsC') ws ?wsC') bd ?bdC') ?dn' ?dnC') p ?pC') ?v ?vC') ?d ?dC'))) ?cur ?curC) ?st ?stC =>
          let Hpre := fresh "Hpre" in
          assert (Hpre : (φ (snd st) + cnt us (φ v) (M us) <= M us + 1)%Z) by (cbn [snd]; unfold Rem in *; lia);
          pose proof (relax_chain_time n us vs ws HM Hlv Hlw nx Hnx bd p Hlb Hlp L HL nxC' vsC' wsC' bdC' dn' dnC' pC' v vC' d dC' cur curC st stC Hcur Hpre) end end.
      match goal with |- context [chain_fold nx ?f ?cur ?st] =>
        cost_destruct_witness (chain_fold nx f cur st) as [x xC sz2 sz2C] eqn:Ec end.
      cost_simpl. destruct xC as [D2 D2C hp2 hp2C]. cost_simpl.
      subst RHS. rewrite E2, ERem. unfold Rem in *. lia.
Qed.

Arguments dij_body : simpl never.
Lemma dij_acc_time hdC nxC vsC wsC bdC pC limC U : (0 <= U < N n)%Z ->
  forall k steps stepsC st stC H HC, (Z.to_nat (gap (PArray.length us + 1) steps) <= k)%nat -> dok U steps st ->
  (cost (extract (extract (extract (extract (extract (extract (extract (extract (extract (dij_acc_cost stepsCM hd hdC) nx nxC) vs vsC) ws wsC) bd bdC) p pC) (PArray.length us + 1)%uint63 limC) steps stepsC) st stC) H HC)
    <= k * (L * 100 + 500) + Z.to_nat (dpot st) * (L * 80 + 200) + 30)%nat.
Proof.
  intros HU k0 steps stepsC st stC H HC Hk HI.
  unfold dij_acc_cost. cbn.
  match goal with |- context [@cost ?T (?G hd hdC nx nxC vs vsC ws wsC bd bdC p pC (PArray.length us + 1)%uint63 limC steps stepsC st stC H HC)] =>
    assert (HG : forall k steps stepsC st stC H HC, (Z.to_nat (gap (PArray.length us + 1) steps) <= k)%nat -> dok U steps st ->
       (cost (G hd hdC nx nxC vs vsC ws wsC bd bdC p pC (PArray.length us + 1)%uint63 limC steps stepsC st stC H HC)
         <= k * (L * 100 + 500) + Z.to_nat (dpot st) * (L * 80 + 200) + 30)%nat) end.
  { pose proof (lim_phi us) as Elim. pose proof (M_nonneg us vs ws Hlv Hlw) as M0.
    induction k as [|k IH]; intros st' stepsC' st2 stC' [g] HC' Hk' HI';
      destruct stC' as [x xC sz szC]; destruct xC as [y yC hp hpC]; destruct yC as [D DC dn dnC];
      cost_simpl_h dij_acc;
      zero_if (0 <? sz);
      repeat match goal with |- context [@cost ?T ?X] =>
        lazymatch X with bdec_cost stepsCM ?b ?w => gen_with T X (bdec_time b w) end end;
      cost_destruct (bdec ((0 <? sz) && (st' <? PArray.length us + 1))); cost_simpl; [| lia | | lia].
    - exfalso. pose proof e as e'. apply andb_prop in e'. destruct e' as [_ e']. rewrite ltb_spec in e'. unfold gap in Hk'. lia.
    - pose proof e as e'. apply andb_prop in e'. destruct e' as [E1 E2]. rewrite ltb_spec in E1, E2. change (φ 0) with 0%Z in E1.
      zl dij_body_cost 6%nat.
      match goal with |- context [@cost ?T ?X] =>
        lazymatch X with extract (extract (extract (extract (extract (extract (dij_body_cost stepsCM hd ?a1) nx ?a2) vs ?a3) ws ?a4) bd ?a5) p ?a6) ?st0 ?stc0 =>
          pose proof (dij_body_time a1 a2 a3 a4 a5 a6 U st' st0 stc0 HU HI' E1) end end.
      assert (HI2 : dok U (st' + 1) (dij_body hd nx vs ws bd p (D, dn, hp, sz))).
      { exact (dij_step n us vs ws Hn HM Hlv Hlw Hend Hwt hd nx Hhd Hnx bd p Hlb Hlp Hfeas Hpb Hshort U D dn hp sz st' HU HI' E1 ltac:(rewrite <- Elim; exact E2)). }
      assert (Hk2 : (Z.to_nat (gap (PArray.length us + 1) (st' + 1)) <= k)%nat).
      { assert (Es : φ (st' + 1) = (φ st' + 1)%Z) by (apply phi_add1; lia). unfold gap in *. lia. }
      match goal with |- context [@cost ?T (F hd hdC nx nxC vs vsC ws wsC bd bdC p pC (PArray.length us + 1)%uint63 limC (st' + 1)%uint63 ?w ?st3 ?stc3 ?hh ?ee)] =>
        pose proof (IH (st' + 1)%uint63 w st3 stc3 hh ee Hk2 HI2) end.
      match goal with HB : context [dpot (D, dn, hp, sz)] |- _ => change (dpot (D, dn, hp, sz)) with (Rem us dn) in HB end.
      lia. }
  match goal with |- context [@cost ?T (?G hd hdC nx nxC vs vsC ws wsC bd bdC p pC (PArray.length us + 1)%uint63 limC steps stepsC st stC H HC)] =>
    exact (HG _ steps stepsC st stC H HC Hk HI : (@cost T (G hd hdC nx nxC vs vsC ws wsC bd bdC p pC (PArray.length us + 1)%uint63 limC steps stepsC st stC H HC) <= _)%nat) end.
Qed.

End CostDij.

(* ---- cdev.v ---- *)
Lemma for_acc_time_r S SC f fC (K : nat) (lo : Z) hi :
  (forall i iC s sC, (lo <= φ i < φ hi)%Z -> (cost (fC i iC) + cost (extract (fC i iC) s sC) <= K)%nat) ->
  forall hiC i iC s sC H HC, (lo <= φ i)%Z ->
  (cost (extract (extract (extract (extract (extract (for_acc_cost stepsCM S SC) f fC) hi hiC) i iC) s sC) H HC)
    <= (K + 20) * Z.to_nat (gap hi i) + 10)%nat.
Proof.
  intros HK hiC i iC s sC H HC Hlo.
  unfold for_acc_cost. cbn.
  match goal with |- context [@cost ?T (?G hi hiC i iC s sC H HC)] =>
    assert (HG : forall k i iC s sC H HC, (Z.to_nat (gap hi i) <= k)%nat -> (lo <= φ i)%Z ->
       (cost (G hi hiC i iC s sC H HC) <= (K + 20) * k + 10)%nat) end.
  { induction k as [|k IH]; intros i' iC' s' sC' [g] HC' Hk Hl;
      cost_simpl;
      pose proof (bdec_time (i' <? hi) (bool_w (i' <? hi))) as HB;
      cost_destruct (bdec (i' <? hi)); cost_simpl.
    - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e). unfold gap in Hk. lia.
    - lia.
    - pose proof (proj1 (Uint63.ltb_spec _ _) e) as Hlt.
      assert (E1 : φ (i' + 1) = (φ i' + 1)%Z) by (zify; Z.to_euclidean_division_equations; lia).
      assert (Hk' : (Z.to_nat (gap hi (i' + 1)) <= k)%nat) by (unfold gap in *; lia).
      match goal with |- context [@cost ?T (?G' hi hiC (i' + 1)%uint63 ?w ?s2 ?sc2 ?h ?e2)] =>
          pose proof (IH (i' + 1)%uint63 w s2 sc2 h e2 Hk' ltac:(lia) : (@cost T (G' hi hiC (i' + 1)%uint63 w s2 sc2 h e2) <= _)%nat) end.
      specialize (HK i' iC' s' sC' ltac:(lia)). cost_align HK. lia.
    - lia. }
  match goal with |- context [@cost ?T (?G hi hiC i iC s sC H HC)] =>
    exact (HG _ i iC s sC H HC (le_n _) Hlo : (@cost T (G hi hiC i iC s sC H HC) <= _)%nat) end.
Qed.

Lemma for_loop_time_r S SC f fC (K : nat) lo hi :
  (forall i iC s sC, (φ lo <= φ i < φ hi)%Z -> (cost (fC i iC) + cost (extract (fC i iC) s sC) <= K)%nat) ->
  forall loC hiC s sC,
  (cost (extract (extract (extract (extract (for_loop_cost stepsCM S SC) f fC) lo loC) hi hiC) s sC)
    <= (K + 20) * Z.to_nat (gap hi lo) + 20)%nat.
Proof.
  intros HK loC hiC s sC.
  unfold for_loop_cost. cost_simpl. zl for_acc_cost 5%nat.
  match goal with |- context [@cost ?T (extract (extract (extract (extract (extract (for_acc_cost stepsCM S SC) f fC) hi hiC) lo loC) s sC) ?h ?hc)] =>
    pose proof (for_acc_time_r S SC f fC K (φ lo) hi HK hiC lo loC s sC h hc ltac:(lia) : (@cost T (extract (extract (extract (extract (extract (for_acc_cost stepsCM S SC) f fC) hi hiC) lo loC) s sC) h hc) <= _)%nat) end.
  lia.
Qed.

Ltac gen_for_loop_r K tac := match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (for_loop_cost stepsCM ?S ?SC) ?f ?fC) ?lo ?loC) ?hi ?hiC) ?s ?sC =>
    let HK := fresh "HK" in
    assert (HK : forall i iC s0 sC0, (φ lo <= φ i < φ hi)%Z -> (cost (fC i iC) + cost (extract (fC i iC) s0 sC0) <= K)%nat) by tac;
    pose proof (for_loop_time_r S SC f fC K lo hi HK loC hiC s sC) end end.

Ltac gen_for_loop_t K tac := match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (for_loop_cost stepsCM ?S ?SC) ?f ?fC) ?lo ?loC) ?hi ?hiC) ?s ?sC =>
    let HK := fresh "HK" in
    assert (HK : forall i iC s0 sC0, (cost (fC i iC) + cost (extract (fC i iC) s0 sC0) <= K)%nat) by tac;
    pose proof (for_loop_time S SC f fC K HK lo loC hi hiC s sC) end end.

Ltac cost_simpl_nf := cbn; cost_reduce; fold_cost; repeat (cost_rewrite; cost_reduce); cbn; fold_cost.
Ltac split1_nf := gen_elems; first [ cell_split | match goal with |- context [bool_cost stepsCM ?b] =>
  lazymatch b with true => fail | false => fail | _ => cost_destruct b end end
  | match goal with |- context [bool_w ?b] =>
  lazymatch b with true => fail | false => fail | _ => cost_destruct b end end ]; cost_simpl_nf.
Ltac split_ifs_nf := repeat split1_nf; sets.

Section CostDij.
Variables (n : int) (us vs ws : array int).
Hypothesis Hn : (1 <= N n <= 150)%Z.
Hypothesis HM : (M us <= 5000)%Z.
Hypothesis Hlv : PArray.length vs = PArray.length us.
Hypothesis Hlw : PArray.length ws = PArray.length us.
Hypothesis Hend : forall k, (0 <= k < M us)%Z -> (0 <= au us k < N n /\ 0 <= av vs k < N n)%Z.
Hypothesis Hwt : forall k, (0 <= k < M us)%Z -> (-1000 <= aw ws k <= 1000)%Z.
Variables (hd nx : array int).
Hypothesis Hhd : forall a, (0 <= a < N n)%Z -> at_ hd a = Lb us a (M us).
Hypothesis Hnx : forall e, (0 <= e < M us)%Z -> at_ nx e = Lb us (au us e) e.
Variables (bd : array bool) (p : array int).
Hypothesis Hlb : PArray.length bd = n.
Hypothesis Hlp : PArray.length p = n.
Hypothesis Hfeas : forall a b w, Gs us vs ws bd a b w -> (sat p b <= sat p a + w)%Z.
Hypothesis Hpb : forall v, (0 <= v < N n)%Z -> (- 1000 * (N n - 1) <= sat p v <= 0)%Z.
Hypothesis Hshort : forall x y c L, pw (Gs us vs ws bd) x y c L -> (0 <= x < N n)%Z ->
  exists c' L', pw (Gs us vs ws bd) x y c' L' /\ (c' <= c)%Z /\ (Z.of_nat (List.length L') <= N n)%Z.
Variable L : nat.
Hypothesis HL : (M us + 1 < 2 ^ Z.of_nat L)%Z.

Arguments dij_body : simpl never.

Lemma dijkstra_time nC mC hdC nxC vsC wsC bdC pC u uC : (0 <= φ u < N n)%Z ->
  (cost (extract (extract (extract (extract (extract (extract (extract (extract (dijkstra_cost stepsCM n nC) (PArray.length us) mC) hd hdC) nx nxC) vs vsC) ws wsC) bd bdC) p pC) u uC)
    <= (Z.to_nat (M us) + 1) * (L * 100 + 500) + Z.to_nat (M us) * (L * 80 + 200) + 100)%nat.
Proof.
  intros Hu. match goal with |- (_ <= ?r)%nat => remember r as RHS eqn:ER end.
  pose proof (lim_phi us) as Elim. pose proof (M_nonneg us vs ws Hlv Hlw) as M0.
  unfold dijkstra_cost. cost_simpl. sets. zl dij_acc_cost 9%nat.
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with extract (extract (extract (extract (extract (extract (extract (extract (extract (dij_acc_cost stepsCM hd ?a1) nx ?a2) vs ?a3) ws ?a4) bd ?a5) p ?a6) ?lim ?limC') ?st0 ?stC0) ?s ?sC) ?H ?HC =>
      pose proof (dij_acc_time n us vs ws Hn HM Hlv Hlw Hend Hwt hd nx Hhd Hnx bd p Hlb Hlp Hfeas Hpb Hshort L HL a1 a2 a3 a4 a5 a6 limC' (φ u) Hu _ st0 stC0 s sC H HC (le_n _)
        (dij_init n us vs ws Hn HM Hlv Hlw bd p Hlb Hlp u Hu)) end end.
  match goal with HH : context [dpot] |- _ => rename HH into HD end.
  cbn [dpot] in HD. unfold Rem in HD. rewrite (remc_all n us vs ws Hlv Hlw) in HD.
  assert (Eg : Z.to_nat (gap (PArray.length us + 1) 0) = (Z.to_nat (M us) + 1)%nat) by (unfold gap; rewrite Elim; change (φ 0) with 0%Z; lia).
  rewrite Eg, Nat2Z.id in HD.
  subst RHS. lia.
Qed.

Lemma row_of_time nC mC hdC nxC vsC wsC R RC bdC pC u uC : (0 <= φ u < N n)%Z ->
  (cost (extract (extract (extract (extract (extract (extract (extract (extract (extract (row_of_cost stepsCM n nC) (PArray.length us) mC) hd hdC) nx nxC) vs vsC) ws wsC) R RC) bd bdC) p pC) u uC)
    <= Z.to_nat (N n) * 500 + (Z.to_nat (M us) + 1) * (L * 200 + 800) + 600)%nat.
Proof.
  intros Hu. match goal with |- (_ <= ?r)%nat => remember r as RHS eqn:ER end.
  unfold row_of_cost. cost_simpl. sets. zl for_loop_cost 4%nat. zl negseed_step_cost 4%nat. zl closure_cost 4%nat. zl dijkstra_cost 8%nat.
  gen_for_loop_t 40%nat ltac:(intros i iC s0 sC0; cbn [Nat.add];
    match goal with |- (cost ?X + cost ?Y <= _)%nat => change (cost X) with 0%nat end;
    apply negseed_step_time).
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with extract (extract (extract (extract (closure_cost stepsCM n ?nC') hd ?hdC') nx ?nxC') vs ?vsC') ?sd ?sdC =>
      pose proof (closure_time n us vs ws Hn HM Hlv Hlw Hend hd hdC' nx nxC' vsC' nC' sd sdC Hhd Hnx) end end.
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with extract (extract (extract (extract (extract (extract (extract (extract (dijkstra_cost stepsCM n ?a0) _ ?a1) hd ?a2) nx ?a3) vs ?a4) ws ?a5) bd ?a6) p ?a7) u ?a8 =>
      pose proof (dijkstra_time a0 a1 a2 a3 a4 a5 a6 a7 u a8 Hu) end end.
  gen_for_loop_t 100%nat ltac:(intros i iC s0 sC0; cost_simpl; sets; zl cell_cost 6%nat;
    match goal with |- context [@cost ?T ?X] =>
      lazymatch X with extract (extract (extract (extract (extract (extract (cell_cost stepsCM ?a0 ?a1) ?a2 ?a3) ?a4 ?a5) ?a6 ?a7) ?a8 ?a9) ?b0 ?b1) ?b2 ?b3 =>
        pose proof (cell_time a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 b0 b1 b2 b3) end end; lia).
  subst RHS. unfold gap in *. change (φ 0) with 0%Z in *. rewrite Z.sub_0_r in *. unfold N in *. lia.
Qed.


Definition rowK : nat := (Z.to_nat (N n) * 500 + (Z.to_nat (M us) + 1) * (L * 200 + 800) + 700)%nat.

Lemma rows_time nC mC hdC nxC vsC wsC R RC bdC pC :
  (cost (extract (extract (extract (extract (extract (extract (extract (extract (apsp_rows_cost stepsCM n nC) (PArray.length us) mC) hd hdC) nx nxC) vs vsC) ws wsC) R RC) bd bdC) p pC)
    <= (rowK + 20) * Z.to_nat (N n) + 40)%nat.
Proof.
  match goal with |- (_ <= ?r)%nat => remember r as RHS eqn:ER end.
  unfold apsp_rows_cost. cost_simpl. sets. zl for_loop_cost 4%nat.
  gen_for_loop_r rowK ltac:(intros i iC s0 sC0 Hi; cost_simpl_nf; sets; zl row_of_cost 9%nat;
      match goal with |- context [@cost ?T ?X] =>
        lazymatch X with extract (extract (extract (extract (extract (extract (extract (extract (extract (row_of_cost stepsCM n ?a0) _ ?a1) hd ?a2) nx ?a3) vs ?a4) ws ?a5) ?R' ?RC') bd ?bdC') p ?pC') i ?uC =>
          gen_with T X (row_of_time a0 a1 a2 a3 a4 a5 R' RC' bdC' pC' i uC ltac:(change (φ 0) with 0%Z in Hi; unfold N; lia)) end end;
      unfold rowK; lia).
  subst RHS. unfold gap in *. change (φ 0) with 0%Z in *. rewrite Z.sub_0_r in *. unfold N in *. lia.
Qed.
End CostDij.




Ltac gen_wit := repeat match goal with |- context [@extract ?CM ?T ?m] =>
  lazymatch T with
  | array_cost _ _ _ _ => idtac | int_cost _ _ => idtac | bool_cost _ _ => idtac | prod_cost _ _ _ _ _ _ => idtac
  end;
  let w := fresh "w" in generalize (@extract CM T m); intro w end.


Ltac gen_bf tac := match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (extract (bf_cost stepsCM ?n ?nC) ?m ?mC) ?us ?usC) ?vs ?vsC) ?ws ?wsC) ?keep ?keepC =>
    let HKk := fresh "HKk" in
    assert (HKk : forall k kC, (cost (keepC k kC) <= 40)%nat) by tac;
    gen_with T X (bf_time n nC m mC us usC vs vsC ws wsC keep keepC 40 HKk) end end.


(* the final arithmetic: the costs and the sizes as variables *)
Ltac nat_close := 
  repeat match goal with H : forall _, _ |- _ => clear H end;
  repeat match goal with H : (_ <= _)%nat |- _ => revert H end;
  repeat match goal with |- context [@cost ?T ?X] => generalize (@cost T X); intros ? end;
  intros;
  repeat match goal with H : ?T |- _ => lazymatch T with (_ <= _)%nat => fail | _ => clear H end end.

Section CostG3.
Variables (n : int) (us vs ws : array int).
Hypothesis Hn : (1 <= N n <= 150)%Z.
Hypothesis HM : (M us <= 5000)%Z.
Hypothesis Hlv : PArray.length vs = PArray.length us.
Hypothesis Hlw : PArray.length ws = PArray.length us.
Hypothesis Hend : forall k, (0 <= k < M us)%Z -> (0 <= au us k < N n /\ 0 <= av vs k < N n)%Z.
Hypothesis Hwt : forall k, (0 <= k < M us)%Z -> (-1000 <= aw ws k <= 1000)%Z.
Variable L : nat.
Hypothesis HL : (M us + 1 < 2 ^ Z.of_nat L)%Z.

Lemma core_time hd nx nC mC usC vsC wsC hdC nxC
  (Hhd : forall a, (0 <= a < N n)%Z -> at_ hd a = Lb us a (M us))
  (Hnx : forall e, (0 <= e < M us)%Z -> at_ nx e = Lb us (au us e) e) :
  (cost (extract (extract (extract (extract (extract (extract (apsp_core_cost stepsCM n nC) (PArray.length us) mC) us usC) vs vsC) ws wsC) hd hdC) nx nxC)
    <= Z.to_nat (N n) * (Z.to_nat (N n) * 1000 + (Z.to_nat (M us) + 1) * (L * 200 + 1200) + 2000) + Z.to_nat (M us) * 200 + 900)%nat.
Proof.
  match goal with |- (_ <= ?r)%nat => remember r as RHS eqn:ER end.
  pose proof (M_nonneg us vs ws Hlv Hlw) as M0.
  destruct (dij_hyps n us vs ws Hn HM Hlv Hlw Hend Hwt hd nx Hhd Hnx) as (B1 & B2 & B3 & B4 & B5).
  unfold apsp_core_cost. cost_simpl.
  zl reach_matrix_cost 3%nat. zl bf_cost 5%nat. zl for_loop_cost 4%nat. zl bad_step_cost 6%nat. zl apsp_rows_cost 8%nat. sets.
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with extract (extract (extract (reach_matrix_cost stepsCM n ?a0) hd ?a1) nx ?a2) vs ?a3 =>
      gen_with T X (reach_matrix_time n us vs ws Hn HM Hlv Hlw Hend hd a1 nx a2 a3 a0 Hhd Hnx) end end.
  gen_bf ltac:(intros k kC; cost_simpl_nf; lia).
  gen_bf ltac:(intros k kC; cost_simpl_nf; split_ifs_nf; lia).
  gen_for_loop_t 60%nat ltac:(intros i iC s0 sC0; cbn [Nat.add];
    match goal with |- (cost ?X + cost ?Y <= _)%nat => change (cost X) with 0%nat end;
    apply bad_step_time).
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with extract (extract (extract (extract (extract (extract (extract (extract (apsp_rows_cost stepsCM n ?a0) _ ?a1) hd ?a2) nx ?a3) vs ?a4) ws ?a5) ?R ?RC) ?bd ?bdC) ?p ?pC =>
      gen_with T X (rows_time n us vs ws Hn HM Hlv Hlw Hend Hwt hd nx Hhd Hnx (bad n us vs ws hd nx) (pot n us vs ws hd nx) B1 B2 B3 B4 B5 L HL a0 a1 a2 a3 a4 a5 R RC bdC pC) end end.
  subst RHS. unfold rowK in *. nat_close.
  repeat match goal with H : context [gap _ _] |- _ => unfold gap in H end.
  change (φ 0) with 0%Z in *. rewrite ?Z.sub_0_r in *. unfold N, M in *.
  set (Nn := Z.to_nat (φ n)) in *. set (Mn := Z.to_nat (φ (PArray.length us))) in *.
  clearbody Nn Mn. lia.
Qed.

Lemma impl_time nC usC vsC wsC :
  (cost (extract (extract (extract (allpairspath_impl_cost stepsCM n nC) us usC) vs vsC) ws wsC)
    <= Z.to_nat (N n) * (Z.to_nat (N n) * 1000 + (Z.to_nat (M us) + 1) * (L * 200 + 1200) + 2000) + Z.to_nat (M us) * 300 + 1100)%nat.
Proof.
  match goal with |- (_ <= ?r)%nat => remember r as RHS eqn:ER end.
  unfold allpairspath_impl_cost. cost_simpl. zl build_adj_cost 2%nat.
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with extract (extract (build_adj_cost stepsCM n ?a0) ?m ?a1) us ?a2 =>
      pose proof (build_adj_time n a0 m a1 us a2) end end.
  match goal with |- context [build_adj n ?m us] =>
    cost_destruct_witness (build_adj n m us) as [hd hdC nx nxC] eqn:Eb end.
  destruct (build_adj_spec n us vs ws Hn Hlv Hlw Hend hd nx Eb) as (_ & _ & Hhd & Hnx).
  cost_simpl. zl apsp_core_cost 6%nat.
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with extract (extract (extract (extract (extract (extract (apsp_core_cost stepsCM n ?a0) _ ?a1) us ?a2) vs ?a3) ws ?a4) hd ?a5) nx ?a6 =>
      gen_with T X (core_time hd nx a0 a1 a2 a3 a4 a5 a6 Hhd Hnx) end end.
  subst RHS. nat_close.
  unfold N, M in *.
  set (Nn := Z.to_nat (φ n)) in *. set (Mn := Z.to_nat (φ (PArray.length us))) in *.
  clearbody Nn Mn. lia.
Qed.

End CostG3.

Theorem allpairspath_time : exists c1 c2 : nat,
  forall (node_count : BinNums.N)
  (edge_sources edge_targets : list BinNums.N)
  (edge_weights : list Z)
  (node_count_int : uint)
  (edge_sources_arr edge_targets_arr : array uint)
  (edge_weights_arr : array sint),
  valid_input node_count edge_sources edge_targets
  edge_weights ->
  repr node_count_int node_count ->
  repr edge_sources_arr edge_sources
  -> repr edge_targets_arr edge_targets ->
  repr edge_weights_arr edge_weights ->
  (cost4 allpairspath_cost node_count_int edge_sources_arr edge_targets_arr edge_weights_arr <= c1 * ((size node_count_int + 1) * (size node_count_int + size edge_sources_arr + 1) * (Nat.log2 (size node_count_int + size edge_sources_arr) + 1)) + c2)%nat.
Proof.
  exists (1000 * 6)%nat, 2000%nat.
  intros nN lu lv lw xn xu xv xw Hvi Hrn Hru Hrv Hrw.
  match goal with |- (_ <= ?r)%nat => remember r as RHS eqn:ER end.
  pose proof (Fn nN xn Hrn) as HFn. destruct (Flens nN lu lv lw xu xv xw Hvi Hru Hrv Hrw) as (Lu & Lv & Lw).
  pose proof Hvi as Hvi'. destruct Hvi' as [Hn0 Hm0 _ _ Hend0 Hwt0]. unfold len in Hm0.
  assert (LuM : M xu = Z.of_nat (List.length lu)) by exact Lu.
  assert (HnZ : (1 <= N xn <= 150)%Z) by (unfold N; lia).
  assert (HMZ : (M xu <= 5000)%Z) by lia.
  assert (Hend' : forall k, (0 <= k < M xu)%Z -> (0 <= au xu k < N xn /\ 0 <= av xv k < N xn)%Z).
  { intros k Hk. rewrite LuM in Hk. unfold N.
    destruct (Hend0 (Z.to_N k) ltac:(unfold edge_index, len; lia)) as [A B].
    unfold vertex, get_list_N in A, B. rewrite Z_N_nat in A, B.
    rewrite (au_list lu xu Hru) by lia. rewrite (av_list lv xv Hrv) by (destruct Hvi as [_ _ X _ _ _]; unfold len in X; lia).
    lia. }
  assert (Hwt' : forall k, (0 <= k < M xu)%Z -> (-1000 <= aw xw k <= 1000)%Z).
  { intros k Hk. rewrite LuM in Hk.
    destruct Hvi as [_ _ _ X _ _]. unfold len in X.
    rewrite (aw_list lw xw Hrw) by lia.
    rewrite Forall_forall in Hwt0. apply Hwt0. apply nth_In. lia. }
  pose proof (M_nonneg xu xv xw Lv Lw) as M0.
  assert (ENn : size xn = Z.to_nat (N xn)) by reflexivity.
  assert (EMn : size xu = Z.to_nat (M xu)) by reflexivity.
  set (Lg := Nat.log2 (size xn + size xu)) in *.
  assert (HL : (M xu + 1 < 2 ^ Z.of_nat (Lg + 1))%Z).
  { assert (Hpos : (0 < size xn + size xu)%nat) by (rewrite ENn; lia).
    destruct (Nat.log2_spec (size xn + size xu) Hpos) as [_ H2].
    fold Lg in H2. replace (S Lg) with (Lg + 1)%nat in H2 by lia.
    assert (E2 : (2 ^ Z.of_nat (Lg + 1))%Z = Z.of_nat (2 ^ (Lg + 1))) by (rewrite Nat2Z.inj_pow; reflexivity).
    rewrite E2. apply Nat2Z.inj_lt in H2. rewrite ENn, EMn in H2.
    set (P := (2 ^ (Lg + 1))%nat) in *. clearbody P. lia. }
  unfold cost4. zl allpairspath_cost 3%nat. unfold allpairspath_cost.
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with extract (extract (extract (allpairspath_impl_cost stepsCM xn ?a0) xu ?a1) xv ?a2) xw ?a3 =>
      gen_with T X (impl_time xn xu xv xw HnZ HMZ Lv Lw Hend' Hwt' (Lg + 1) HL a0 a1 a2 a3) end end.
  subst RHS. rewrite ENn, EMn in *.
  nat_close.
  set (Nn := Z.to_nat (N xn)) in *. set (Mn := Z.to_nat (M xu)) in *. clearbody Nn Mn Lg.
  assert (P1 : (Nn * Nn <= (Nn + 1) * (Nn + Mn + 1) * (Lg + 1))%nat) by nia.
  assert (P2 : (Nn * (Mn + 1) * (Lg + 1) <= (Nn + 1) * (Nn + Mn + 1) * (Lg + 1))%nat) by nia.
  assert (P3 : (Nn * (Mn + 1) <= (Nn + 1) * (Nn + Mn + 1) * (Lg + 1))%nat) by nia.
  assert (P4 : (Nn + Mn <= (Nn + 1) * (Nn + Mn + 1) * (Lg + 1))%nat) by nia.
  nia.
Qed.
