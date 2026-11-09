(* Correctness proofs for allpairspath_implem.v. *)
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

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import Bool ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Psatz.
From Stdlib Require Sint63.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Require Export allpairspath_implem.
Open Scope uint63_scope.
Open Scope array_scope.


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

Definition allpairspath_correct :
  forall (n : BinNums.N) (us vs : list BinNums.N) (ws : list Z)
         (xn : uint) (xu xv : array uint) (xw : array sint),
  valid_input n us vs ws ->
  repr xn n -> repr xu us -> repr xv vs -> repr xw ws ->
  exists m : list (list (answer Z)),
    repr (allpairspath xn xu xv xw) m /\ allpairspath_spec n us vs ws m
  := final_correct.
