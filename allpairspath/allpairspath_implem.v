(* Executable implementation and its required termination dependencies.
   Correctness proofs are in allpairspath_proofs.v. *)
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

(* ====================================================================== *)
(* The binary heap                                                        *)
(* ====================================================================== *)
Open Scope uint63_scope.
Open Scope array_scope.
Open Scope bool_scope.

Definition swap (t : array int) (i j : int) : array int :=
  let a := t.[i] in
  let b := t.[j] in
  t.[i <- b].[j <- a].

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

(* push and pop *)
Definition hpush (t : array int) (s x : int) : array int :=
  sift_up t.[s <- x] s (Zwf_well_founded 0 (φ s)).

Definition hpop (t : array int) (s : int) : int * array int :=
  let top := t.[0] in
  let s' := s - 1 in
  let last := t.[s'] in
  (top, sift_down t.[0 <- last] s' 0 (Zwf_well_founded 0 (gap s' 0))).

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

Definition build_adj (n m : int) (us : array int) : array int * array int :=
  for_loop (adj_step us) 0 m (PArray.make n 0, PArray.make m 0).

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

(* Breadth-first closure of a set of seeds.  State: marks, queue, tail. *)
Definition bfs_visit (vs : array int) (e : int) (st : array bool * array int * int)
    : array bool * array int * int :=
  let '(mark, q, tl) := st in
  let b := vs.[e] in
  if mark.[b] then st else (mark.[b <- true], q.[tl <- b], tl + 1).

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

Definition seed_step (seed : array bool) (a : int) (st : array bool * array int * int)
    : array bool * array int * int :=
  let '(mark, q, tl) := st in
  if seed.[a] then (mark.[a <- true], q.[tl <- a], tl + 1) else st.

Definition closure (n : int) (hd nx vs : array int) (seed : array bool) : array bool :=
  let st0 := for_loop (seed_step seed) 0 n (PArray.make n false, PArray.make n 0, 0) in
  bfs_acc hd nx vs n 0 st0 (Zwf_well_founded 0 (gap n 0)).

(* The reachability matrix, flat: cell s * n + v. *)
Definition copy_step (n s : int) (row : array bool) (v : int) (r : array bool) : array bool :=
  r.[s * n + v <- row.[v]].

Definition reach_row (n : int) (hd nx vs : array int) (s : int) (r : array bool) : array bool :=
  let row := closure n hd nx vs (PArray.make n false).[s <- true] in
  for_loop (copy_step n s row) 0 n r.

Definition reach_matrix (n : int) (hd nx vs : array int) : array bool :=
  for_loop (reach_row n hd nx vs) 0 n (PArray.make (n * n) false).

(* Bellman-Ford from a virtual source, over the edges k with keep k. *)
Definition bf_edge (us vs ws : array int) (keep : int -> bool) (k : int) (h : array int)
    : array int :=
  if keep k then
    let a := us.[k] in
    let b := vs.[k] in
    let nb := h.[a] + ws.[k] in
    if Sint63.ltb nb h.[b] then h.[b <- nb] else h
  else h.

Definition bf_round (m : int) (us vs ws : array int) (keep : int -> bool) (r : int)
    (h : array int) : array int :=
  for_loop (bf_edge us vs ws keep) 0 m h.

Definition bf (n m : int) (us vs ws : array int) (keep : int -> bool) : array int :=
  for_loop (bf_round m us vs ws keep) 0 n (PArray.make n 0).

(* The sources of the edges inside a strongly connected component that
   still relax after Bellman-Ford over those edges. *)
Definition bad_step (n : int) (us vs ws : array int) (R : array bool) (h : array int)
    (k : int) (bad : array bool) : array bool :=
  let a := us.[k] in
  let b := vs.[k] in
  if R.[b * n + a] && Sint63.ltb (h.[a] + ws.[k]) h.[b] then bad.[a <- true] else bad.

(* Dijkstra with a binary heap of keys d * 256 + v, on the edges between
   good vertices, reweighted by the potentials p. *)
Definition INF : int := 1073741824.

Definition relax (vs ws : array int) (bad done : array bool) (p : array int) (v d : int)
    (e : int) (st : array int * array int * int) : array int * array int * int :=
  let '(D, hp, sz) := st in
  let b := vs.[e] in
  if negb bad.[b] && negb done.[b] then
    let nd := d + ws.[e] + p.[v] - p.[b] in
    if nd <? D.[b] then (D.[b <- nd], hpush hp sz (nd * 256 + b), sz + 1) else st
  else st.

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

Definition dijkstra (n m : int) (hd nx vs ws : array int) (bad : array bool) (p : array int)
    (u : int) : array int :=
  let D0 := (PArray.make n INF).[u <- 0] in
  let hp0 := (PArray.make (m + 1) 0).[0 <- u] in
  dij_acc hd nx vs ws bad p (m + 1) 0 (D0, PArray.make n false, hp0, 1)
    (Zwf_well_founded 0 (gap (m + 1) 0)).

(* One row of the answer. *)
Definition cell (n : int) (R neg : array bool) (D p : array int) (u v : int) : answer int :=
  if neg.[v] then NegInfinity
  else if R.[u * n + v] then Distance (D.[v] - p.[u] + p.[v])
  else Impossible.

Definition negseed_step (n : int) (R bad : array bool) (u a : int) (s : array bool)
    : array bool :=
  if bad.[a] && R.[u * n + a] then s.[a <- true] else s.

Definition row_of (n m : int) (hd nx vs ws : array int) (R bad : array bool) (p : array int)
    (u : int) : array (answer int) :=
  let seed := for_loop (negseed_step n R bad u) 0 n (PArray.make n false) in
  let neg := closure n hd nx vs seed in
  let D := dijkstra n m hd nx vs ws bad p u in
  for_loop (fun v r => r.[v <- cell n R neg D p u v]) 0 n (PArray.make n Impossible).

Definition allpairspath_impl (n : int) (us vs ws : array int) : array (array (answer int)) :=
  let m := PArray.length us in
  let (hd, nx) := build_adj n m us in
  let R := reach_matrix n hd nx vs in
  let h1 := bf n m us vs ws (fun k => R.[vs.[k] * n + us.[k]]) in
  let bad := for_loop (bad_step n us vs ws R h1) 0 m (PArray.make n false) in
  let p := bf n m us vs ws (fun k => negb bad.[us.[k]] && negb bad.[vs.[k]]) in
  for_loop (fun u res => res.[u <- row_of n m hd nx vs ws R bad p u]) 0 n
    (PArray.make n (PArray.make 0 Impossible)).

(* ====================================================================== *)
(* Correctness                                                            *)
(* ====================================================================== *)
Open Scope uint63_scope.
Open Scope array_scope.
Open Scope bool_scope.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition allpairspath : uint -> array uint -> array uint -> array sint ->
                            array (array (answer sint)) := allpairspath_impl.
